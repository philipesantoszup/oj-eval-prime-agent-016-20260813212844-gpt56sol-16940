#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <limits>
#include <string>

// A persistent B+ tree.  Values are part of the key, so equal textual indices
// form one consecutive range in the leaves.
namespace {
constexpr int MAX_KEYS = 96;
constexpr int MIN_KEYS = MAX_KEYS / 2;
constexpr int MAX_NODES = 6600;
constexpr const char *DB_FILE = "bptree.data";

#pragma pack(push, 1)
struct Key {
  char index[65];
  std::int32_t value;
};

struct Node {
  std::uint8_t leaf;
  std::int16_t count;
  std::int32_t parent;
  std::int32_t next;                 // next leaf; also free-list link
  Key keys[MAX_KEYS + 1];            // one overflow slot
  std::int32_t child[MAX_KEYS + 2];  // one overflow child slot
};

struct Header {
  char magic[8];
  std::uint32_t version;
  std::int32_t root;
  std::int32_t node_count;
  std::int32_t free_head;
};
#pragma pack(pop)

Node nodes[MAX_NODES];
bool dirty[MAX_NODES];
Header header{};

int compareKey(const Key &a, const Key &b) {
  int c = std::strcmp(a.index, b.index);
  if (c != 0) return c;
  return (a.value > b.value) - (a.value < b.value);
}

Key makeKey(const std::string &s, int value) {
  Key k{};
  std::memcpy(k.index, s.data(), s.size());
  k.index[s.size()] = '\0';
  k.value = value;
  return k;
}

void mark(int id) { dirty[id] = true; }

int allocateNode(bool leaf) {
  int id;
  if (header.free_head != -1) {
    id = header.free_head;
    header.free_head = nodes[id].next;
  } else {
    if (header.node_count >= MAX_NODES) {
      std::cerr << "B+ tree node capacity exceeded\n";
      std::exit(2);
    }
    id = header.node_count++;
  }
  std::memset(&nodes[id], 0, sizeof(Node));
  nodes[id].leaf = leaf;
  nodes[id].parent = -1;
  nodes[id].next = -1;
  mark(id);
  return id;
}

void releaseNode(int id) {
  nodes[id].count = 0;
  nodes[id].leaf = 0;
  nodes[id].parent = -1;
  nodes[id].next = header.free_head;
  header.free_head = id;
  mark(id);
}

void initialize() {
  std::memset(&header, 0, sizeof(header));
  std::memcpy(header.magic, "BPT2697", 7);
  header.version = 1;
  header.root = -1;
  header.node_count = 0;
  header.free_head = -1;
  header.root = allocateNode(true);
}

void loadDatabase() {
  FILE *f = std::fopen(DB_FILE, "rb");
  if (!f) { initialize(); return; }
  Header h{};
  bool ok = std::fread(&h, sizeof(h), 1, f) == 1 &&
            std::memcmp(h.magic, "BPT2697", 7) == 0 && h.version == 1 &&
            h.node_count > 0 && h.node_count <= MAX_NODES &&
            h.root >= 0 && h.root < h.node_count;
  if (ok) {
    ok = std::fread(nodes, sizeof(Node), h.node_count, f) ==
         static_cast<std::size_t>(h.node_count);
  }
  std::fclose(f);
  if (ok) header = h;
  else initialize();
}

void saveDatabase() {
  FILE *f = std::fopen(DB_FILE, "r+b");
  if (!f) f = std::fopen(DB_FILE, "w+b");
  if (!f) { std::cerr << "cannot open database file\n"; std::exit(3); }
  std::fseek(f, 0, SEEK_SET);
  std::fwrite(&header, sizeof(header), 1, f);
  for (int i = 0; i < header.node_count; ++i) {
    if (!dirty[i]) continue;
    const long long offset = sizeof(Header) + 1LL * i * sizeof(Node);
    std::fseek(f, static_cast<long>(offset), SEEK_SET);
    std::fwrite(&nodes[i], sizeof(Node), 1, f);
  }
  std::fflush(f);
  std::fclose(f);
}

int childPosition(int parent, int id) {
  Node &p = nodes[parent];
  for (int i = 0; i <= p.count; ++i) if (p.child[i] == id) return i;
  return -1;
}

int findLeaf(const Key &key) {
  int id = header.root;
  while (!nodes[id].leaf) {
    Node &n = nodes[id];
    int lo = 0, hi = n.count;
    // Separators are the minimum keys of their right children.
    while (lo < hi) {
      int mid = (lo + hi) / 2;
      if (compareKey(key, n.keys[mid]) < 0) hi = mid;
      else lo = mid + 1;
    }
    id = n.child[lo];
  }
  return id;
}

int lowerPosition(const Node &n, const Key &key) {
  int lo = 0, hi = n.count;
  while (lo < hi) {
    int mid = (lo + hi) / 2;
    if (compareKey(n.keys[mid], key) < 0) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

// Inform ancestors that the minimum key in this subtree has changed.
void propagateMinimum(int id, const Key &minimum) {
  int parent = nodes[id].parent;
  if (parent == -1) return;
  int pos = childPosition(parent, id);
  if (pos > 0) {
    nodes[parent].keys[pos - 1] = minimum;
    mark(parent);
  } else {
    propagateMinimum(parent, minimum);
  }
}

void insertInParent(int left, const Key &separator, int right);

void splitInternal(int id) {
  Node &n = nodes[id];
  const int middle = n.count / 2;
  Key promoted = n.keys[middle];
  int right = allocateNode(false);
  Node &r = nodes[right];
  r.parent = n.parent;
  r.count = n.count - middle - 1;
  for (int i = 0; i < r.count; ++i) r.keys[i] = n.keys[middle + 1 + i];
  for (int i = 0; i <= r.count; ++i) {
    r.child[i] = n.child[middle + 1 + i];
    nodes[r.child[i]].parent = right;
    mark(r.child[i]);
  }
  n.count = middle;
  mark(id); mark(right);
  insertInParent(id, promoted, right);
}

void insertInParent(int left, const Key &separator, int right) {
  int parent = nodes[left].parent;
  if (parent == -1) {
    int root = allocateNode(false);
    nodes[root].count = 1;
    nodes[root].child[0] = left;
    nodes[root].child[1] = right;
    nodes[root].keys[0] = separator;
    nodes[left].parent = root;
    nodes[right].parent = root;
    header.root = root;
    mark(root); mark(left); mark(right);
    return;
  }
  Node &p = nodes[parent];
  int pos = childPosition(parent, left);
  for (int i = p.count; i > pos; --i) p.keys[i] = p.keys[i - 1];
  for (int i = p.count + 1; i > pos + 1; --i) p.child[i] = p.child[i - 1];
  p.keys[pos] = separator;
  p.child[pos + 1] = right;
  ++p.count;
  nodes[right].parent = parent;
  mark(parent); mark(right);
  if (p.count > MAX_KEYS) splitInternal(parent);
}

void insertKey(const Key &key) {
  int leaf = findLeaf(key);
  Node &n = nodes[leaf];
  int pos = lowerPosition(n, key);
  if (pos < n.count && compareKey(n.keys[pos], key) == 0) return;
  for (int i = n.count; i > pos; --i) n.keys[i] = n.keys[i - 1];
  n.keys[pos] = key;
  ++n.count;
  mark(leaf);
  if (pos == 0) propagateMinimum(leaf, n.keys[0]);
  if (n.count <= MAX_KEYS) return;

  const int cut = n.count / 2;
  int right = allocateNode(true);
  Node &r = nodes[right];
  r.parent = n.parent;
  r.next = n.next;
  r.count = n.count - cut;
  for (int i = 0; i < r.count; ++i) r.keys[i] = n.keys[cut + i];
  n.count = cut;
  n.next = right;
  mark(leaf); mark(right);
  insertInParent(leaf, r.keys[0], right);
}

void removeChildAndSeparator(int parent, int right_child_pos) {
  Node &p = nodes[parent];
  int key_pos = right_child_pos - 1;
  for (int i = key_pos; i < p.count - 1; ++i) p.keys[i] = p.keys[i + 1];
  for (int i = right_child_pos; i < p.count; ++i) p.child[i] = p.child[i + 1];
  --p.count;
  mark(parent);
}

void rebalanceInternal(int id);

void finishParentAfterRemoval(int parent) {
  Node &p = nodes[parent];
  if (parent == header.root) {
    if (p.count == 0) {
      int new_root = p.child[0];
      nodes[new_root].parent = -1;
      header.root = new_root;
      mark(new_root);
      releaseNode(parent);
    }
  } else if (p.count < MIN_KEYS) {
    rebalanceInternal(parent);
  }
}

void rebalanceLeaf(int id) {
  Node &n = nodes[id];
  int parent = n.parent;
  int pos = childPosition(parent, id);
  Node &p = nodes[parent];
  if (pos > 0) {
    int left_id = p.child[pos - 1];
    Node &left = nodes[left_id];
    if (left.count > MIN_KEYS) {
      for (int i = n.count; i > 0; --i) n.keys[i] = n.keys[i - 1];
      n.keys[0] = left.keys[--left.count];
      ++n.count;
      p.keys[pos - 1] = n.keys[0];
      mark(left_id); mark(id); mark(parent);
      return;
    }
  }
  if (pos < p.count) {
    int right_id = p.child[pos + 1];
    Node &right = nodes[right_id];
    if (right.count > MIN_KEYS) {
      n.keys[n.count++] = right.keys[0];
      for (int i = 0; i < right.count - 1; ++i) right.keys[i] = right.keys[i + 1];
      --right.count;
      p.keys[pos] = right.keys[0];
      mark(right_id); mark(id); mark(parent);
      return;
    }
  }
  if (pos > 0) {
    int left_id = p.child[pos - 1];
    Node &left = nodes[left_id];
    for (int i = 0; i < n.count; ++i) left.keys[left.count + i] = n.keys[i];
    left.count += n.count;
    left.next = n.next;
    removeChildAndSeparator(parent, pos);
    mark(left_id);
    releaseNode(id);
  } else {
    int right_id = p.child[1];
    Node &right = nodes[right_id];
    for (int i = 0; i < right.count; ++i) n.keys[n.count + i] = right.keys[i];
    n.count += right.count;
    n.next = right.next;
    removeChildAndSeparator(parent, 1);
    mark(id);
    releaseNode(right_id);
  }
  finishParentAfterRemoval(parent);
}

void rebalanceInternal(int id) {
  Node &n = nodes[id];
  int parent = n.parent;
  int pos = childPosition(parent, id);
  Node &p = nodes[parent];
  if (pos > 0) {
    int left_id = p.child[pos - 1];
    Node &left = nodes[left_id];
    if (left.count > MIN_KEYS) {
      for (int i = n.count; i > 0; --i) n.keys[i] = n.keys[i - 1];
      for (int i = n.count + 1; i > 0; --i) n.child[i] = n.child[i - 1];
      n.keys[0] = p.keys[pos - 1];
      n.child[0] = left.child[left.count];
      nodes[n.child[0]].parent = id;
      p.keys[pos - 1] = left.keys[left.count - 1];
      --left.count; ++n.count;
      mark(left_id); mark(id); mark(parent); mark(n.child[0]);
      return;
    }
  }
  if (pos < p.count) {
    int right_id = p.child[pos + 1];
    Node &right = nodes[right_id];
    if (right.count > MIN_KEYS) {
      n.keys[n.count] = p.keys[pos];
      n.child[n.count + 1] = right.child[0];
      nodes[n.child[n.count + 1]].parent = id;
      ++n.count;
      p.keys[pos] = right.keys[0];
      for (int i = 0; i < right.count; ++i) right.child[i] = right.child[i + 1];
      for (int i = 0; i < right.count - 1; ++i) right.keys[i] = right.keys[i + 1];
      --right.count;
      mark(right_id); mark(id); mark(parent); mark(n.child[n.count]);
      return;
    }
  }
  if (pos > 0) {
    int left_id = p.child[pos - 1];
    Node &left = nodes[left_id];
    int base = left.count;
    left.keys[base] = p.keys[pos - 1];
    for (int i = 0; i < n.count; ++i) left.keys[base + 1 + i] = n.keys[i];
    for (int i = 0; i <= n.count; ++i) {
      left.child[base + 1 + i] = n.child[i];
      nodes[n.child[i]].parent = left_id;
      mark(n.child[i]);
    }
    left.count += 1 + n.count;
    removeChildAndSeparator(parent, pos);
    mark(left_id);
    releaseNode(id);
  } else {
    int right_id = p.child[1];
    Node &right = nodes[right_id];
    int base = n.count;
    n.keys[base] = p.keys[0];
    for (int i = 0; i < right.count; ++i) n.keys[base + 1 + i] = right.keys[i];
    for (int i = 0; i <= right.count; ++i) {
      n.child[base + 1 + i] = right.child[i];
      nodes[right.child[i]].parent = id;
      mark(right.child[i]);
    }
    n.count += 1 + right.count;
    removeChildAndSeparator(parent, 1);
    mark(id);
    releaseNode(right_id);
  }
  finishParentAfterRemoval(parent);
}

void eraseKey(const Key &key) {
  int leaf = findLeaf(key);
  Node &n = nodes[leaf];
  int pos = lowerPosition(n, key);
  if (pos == n.count || compareKey(n.keys[pos], key) != 0) return;
  for (int i = pos; i < n.count - 1; ++i) n.keys[i] = n.keys[i + 1];
  --n.count;
  mark(leaf);
  if (pos == 0 && n.count > 0) propagateMinimum(leaf, n.keys[0]);
  if (leaf != header.root && n.count < MIN_KEYS) rebalanceLeaf(leaf);
}

void findIndex(const std::string &index) {
  Key low = makeKey(index, std::numeric_limits<int>::min());
  int leaf = findLeaf(low);
  int pos = lowerPosition(nodes[leaf], low);
  bool any = false;
  while (leaf != -1) {
    Node &n = nodes[leaf];
    while (pos < n.count) {
      if (std::strcmp(n.keys[pos].index, index.c_str()) != 0) {
        if (!any) std::cout << "null";
        std::cout << '\n';
        return;
      }
      if (any) std::cout << ' ';
      std::cout << n.keys[pos].value;
      any = true;
      ++pos;
    }
    leaf = n.next;
    pos = 0;
  }
  if (!any) std::cout << "null";
  std::cout << '\n';
}
} // namespace

int main() {
  std::ios::sync_with_stdio(false);
  std::cin.tie(nullptr);
  loadDatabase();
  int n;
  if (!(std::cin >> n)) { saveDatabase(); return 0; }
  std::string command, index;
  int value;
  for (int i = 0; i < n; ++i) {
    std::cin >> command >> index;
    if (command[0] == 'i') {
      std::cin >> value;
      insertKey(makeKey(index, value));
    } else if (command[0] == 'd') {
      std::cin >> value;
      eraseKey(makeKey(index, value));
    } else {
      findIndex(index);
    }
  }
  saveDatabase();
  return 0;
}
