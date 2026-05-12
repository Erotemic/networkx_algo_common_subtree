## Introduction summary (math-relevant)

* The paper considers **rooted ordered trees** (unless explicitly mentioned otherwise).
* An **embedded subtree** is obtained by **contracting edges** (equivalently, deleting matched `0…1` edge-annotation pairs in the encoding).
* The **maximum common embedded subtree** problem is reduced to computing a **longest common balanced sequence** between two encodings.
* The key complexity claim (proved via bounding the number of decomposed subproblems and a DP recurrence) is:

  * `O(n1 n2 min(d1, ℓ1) min(d2, ℓ2))` time on ordered trees with `n1,n2` nodes, depths `d1,d2`, and leaf-counts `ℓ1,ℓ2`.

## Section 2 — Balanced Sequences

Trees will be described by means of a particular form of well-formed parenthesis
strings, called balanced sequences.

**Definition 1.** Let T be a tree with m edges. The balanced sequence of T , denoted
by t, is a sequence over {0, 1} of 2m symbols defined as follows. The balanced
sequence of a leaf node is the empty sequence, and the balanced sequence associated to a nonleaf node is obtained by concatenating the balanced sequences of
the children of the node, each of them preceded by an additional 0 and followed
by an additional 1. The balanced sequence of T is the balanced sequence of the
root of T . A string t over {0, 1} is a balanced sequence if there is a tree T such
that t is the balanced sequence of T .
The length of a balanced sequence x, denoted by |x|, is the number of edges
in the tree described by x, that is, the number of 0 characters or the number
of 1 characters in x. The empty balanced sequence, which describes the tree
with no nodes and no edges, is denoted by λ. Concatenation is indicated by
juxtaposition.

**Remark 1.** Notice that there is a one-to-one correspondence between edges in a
tree and edge annotations in the balanced sequence of the tree.
The previous definition yields a recursive algorithm for obtaining the balanced sequence of a tree.

**Fact 1.** The balanced sequence of a tree can be obtained in time linear in the size
of the tree.

**Remark 2.** The balanced sequence of a tree can also be obtained by performing
a preorder traversal of the tree, adding a 0 each time an edge is first traversed
and adding a 1 each time an edge is traversed in the opposite direction. That is,
by performing a leftmost depth-first traversal of the bidirected graph underlying
the tree, starting at the root, which is equivalent to finding an Euler trail through
the tree [1, Sect. 5.1.2].
A balanced sequence is contained in another balanced sequence if it can be
obtained from the latter by deleting edge annotations (character pairs), that
is, if the tree represented by the former sequence can be embedded in the tree
represented by the latter sequence.

**Definition 2.** A balanced sequence s is said to be contained in a balanced sequence t, denoted by s ⊆ t, if either s = t or there exist balanced sequences
s1, s2, s3 and t1, t2, t3 with si ⊆ti, 1 ≤i ≤3, such that s = s1 s2 s3 and
t = t1 0 t2 1 t3. A longest common balanced sequence of s and t is a balanced
sequence of largest length among all balanced sequences that are contained in
both s and t.

**Example 2.** The balanced sequence 00100100101111 contains the following balanced sequences:

```text
00100100101111 000100101111 0000101111 00001111 000111 0011 01 λ
               001000101111 0001001111 00010111 001011 0101
               001001001111 0001010111 00100111 010011
               001001010111 0010001111 00101011 010101
               001010010111 0010010111 01000111
               010010010111 0010100111 01001011
                            0010101011 01010011
                            0100010111 01010101
                            0100100111
                            0100101011
                            0101001011
```

**Definition 3.** Let s be a nonempty balanced sequence. The head and the tail of
s, denoted respectively by head(s) and tail(s), are the unique balanced sequences
such that s = 0 head(s) 1 tail(s).

**Example 3.** The balanced sequence 001000101101110001000100101110111011 of
the tree from Example 4 can be partitioned into the head 010001011011 and the
tail 0001000100101110111011, both of which are balanced sequences.

```text
0 0 1 0 0 0 1 0 1 1 0 1 1 1 0 0 0 1 0 0 0 1 0 0 1 0 1 1 1 0 1 1 1 0 1 1
  +-------head--------+   +----------------------tail ----------------+
```

**Remark 3.** The partition of the balanced sequence of a tree into a head and a
tail is isomorphic to the partition of a tree into the tree rooted at the first child
and the forest whose first tree is rooted at the next sibling of the first child.

**Definition 4.** Let s be a balanced sequence. The decomposition of s, denoted by
decomp(s), is the set of balanced sequences defined as follows:

– s ∈ decomp(s),
– for all nonempty balanced sequences t ∈ decomp(s),
    • head(t) ∈ decomp(s),
    • tail(t) ∈ decomp(s),
    • head(t) tail(t) ∈ decomp(s),
– no other balanced sequence belongs to decomp(s).

The decomposition of a balanced sequence is thus described by the following
recurrence:

```
D[λ] = {λ}
D[0x1y] = {0x1y} ∪D[x] ∪D[y] ∪D[xy]
```

Now, every sequence in the decomposition of a balanced sequence which is a
suffix of another balanced sequence, belongs to the decomposition of the latter
sequence.

**Lemma 1.** `D[y] ⊆ D[xy]` for all balanced sequences x and y.
*Proof.* By induction on |x|. Let x and y be balanced sequences. If |x| = 0,
D[y] = D[xy]. Otherwise, let x = 0x′1y′. Then,

```
D[y] ⊆D[y′y] (by induction hypothesis)
⊆D[xy] (by definition of D).
```
∎

Now, the recurrences

```
R[λ] = {λ}
S[λ] = {λ}
R[0x1y] = {0x1y} ∪ R[xy]
S[0x1y] = R[x] ∪ S[xy]
```

will also be used in the proof of the next lemmata below.

**Lemma 2.** D[x] ⊆D[xy] ∪R[x] for all balanced sequences x and y.

*Proof.* By induction on |x|. Let x and y be balanced sequences. If |x| = 0,

D[x] = {λ} ⊆D[xy] ∪R[x]. Otherwise, let x = 0x′1y′. Note first that

```
D[x] = {x} ∪D[x′] ∪D[y′] ∪D[x′y′]  (by definition of D)
     = {x} ∪D[x′] ∪D[x′y′]         (by Lemma 1)
```

Moreover, {x} ∈R[x] by definition of R, D[x′] ⊆D[xy] by definition of D and,
further,

```
D[x′y′] ⊆ D[x′y′y] ∪R[x′y′]  (by induction hypothesis)
        ⊆ D[x′y′y] ∪R[x]     (by definition of R)
        ⊆ D[xy] ∪R[x]        (by definition of D)
```

Therefore, it holds that D[x] ⊆D[xy] ∪R[x]. ∎

The previous lemmata combine into the following result.

**Lemma 3.** D[0x1y] ⊆{0x1y}∪D[xy]∪R[x] for all balanced sequences x and y.
*Proof.* Let x and y be balanced sequences. Then,

```
D[0x1y] = {0x1y} ∪ D[x] ∪ D[y] ∪ D[xy]  (by definition of D)
        = {0x1y} ∪ D[x] ∪ D[xy]         (by Lemma 1)
        ⊆ {0x1y} ∪ D[xy] ∪ R[x]         (by Lemma 2). 
```
∎

The main result in this section is an upper bound on the number of sequences
in the decomposition of a balanced sequence.

**Lemma 4.** `D[zy] ⊆D[y] ∪R[x]{y} ∪S[x]` for all z ∈R[x].
*Proof.* By induction on `|z|`. Let `z ∈ R[x]`. If `|z| = 0, D[zy] = D[y] ⊆D[y] ∪ R[x]{y} ∪S[x]`.
Otherwise, let `z = 0x′1y′`. Note first that, by Lemma 3, `D[zy] ⊆ {zy} ∪D[x′y′y] ∪R[x′]`.
Now,

– `{zy} ⊆ R[x]{y}`, by the assumption that `z ∈ R[x]`.

– Since `|x′y′| < |z|` and `x′y′ ∈R[x]`, it follows by induction hypothesis that
D[x′y′y] ⊆D[y] ∪R[x]{y} ∪S[x].

– It can be shown by structural induction in `R[x]` that `R[x′] ⊆ S[x]`. As a
matter of fact, if `z = 0x′1y′ = x`, then `R[x′] ⊆ S[x]`, by definition of S.
Otherwise, `z = 0x′1y′ ≠ x` and, by definition of R, it follows that `z = x′′y′′`
with `0x′′1y′′ ∈ R[x]` and thus, `R[x′] ⊆ S[z] ⊆ S[0x′′1y′′] ⊆ S[x]`, again by
definition of S.

Therefore, `D[zy] ⊆ D[y] ∪ R[x]{y} ∪ S[x]`. ∎

The following results will also be used in the proof of the upper bound on
the cardinal of the decomposition of a balanced sequence.

**Corollary 1.** `D[x] ⊆ R[x] ∪ S[x]` for any balanced sequence x.

*Proof.* For all balanced sequences x, y, since x ∈R[x], it holds by Lemma 4
that D[xy] ⊆D[y] ∪R[x]{y} ∪S[x]. Then, taking y = λ, it follows that D[x] ⊆
{λ} ∪R[x] ∪S[x] = R[x] ∪S[x]. ∎


**Lemma 5.** `S[xy] ⊆ S[x] ∪ S[y]` for all balanced sequences x and y.
*Proof.* By induction on `|x|`. If `|x| = 0, S[xy] = S[y] ⊆ S[y]`. Otherwise, let
x = 0x′1y′. Then,

```
S[0x′1y′y] = R[x′] ∪S[x′y′y]
⊆R[x′] ∪S[x′y′] ∪S[y]        (by induction hypothesis)
⊆S[x] ∪S[y]                  (by definition of S).
```
∎
Now, a bound on the cardinal of R and S will allow one to also bound the
cardinal of D. The following fact is easy to prove by induction.

**Fact 2.** The cardinal of R[x] is equal to |x| + 1, for any balanced sequence x.
Now, the depth and the number of leaves of a balanced sequence t, denoted
respectively by d(t) and ℓ(t), are just the depth and the number of leaves of the
tree represented by t. They are described by the following recurrences:
```
d(λ) = 1
ℓ(λ) = 1
d(0x1y) = max(d(x) + 1, d(y))
ℓ(0x1y) = ℓ(x) + ℓ(y)
```

**Lemma 6.** |S[x]| ≤|x|d(x) + 1 for any balanced sequence x.
*Proof.* By induction on |x|. If |x| = 0, |S[x]| ≤|λ|d(λ) + 1 = 1. Otherwise, let
x = 0x′1y′. By Lemma 5, S[x] ⊆R[x′] ∪S[x′] ∪S[y′] and then,

```
|S[x]| ≤|R[x′]| + |S[x′]| + |S[y′]|
≤|x′| + 1 + |x′|d(x′) + 1 + |y′|d(y′) + 1  (by induction hypothesis)
≤|x′| + |x′|(d(x) -1) + |y′|d(x) + 3       (d(y′), d(x′) + 1 ≤d(x))
= (|x′| + |y′|)d(x) + 3
= (|x| -1)d(x) + 3                         (|x| = |x′| + |y′| + 1)
= |x|d(x) -d(x) + 3
≤|x|d(x) + 1                               (x ≠ λ and d(x) ≥2).
```
∎

**Lemma 7.** `|S[x]| ≤|x|ℓ(x) + 1` for any balanced sequence x.

*Proof.* By induction on `|x|`. If `|x| = 0, |S[x]| ≤|λ|ℓ(λ) + 1 = 1`.
Otherwise, let `x = 0x′1y′`. Then, `S[x] = R[x′]∪S[x′y′] ⊆R[x′]∪S[x′]∪S[y′]`, by Lemma 5, and

```
|S[x]| ≤|R[x′]| + |S[x′]| + |S[y′]|
≤|x′| + 1 + |x′|ℓ(x′) + 1 + |y′|ℓ(y′) + 1   (by induction hypothesis)
= |x′| + |x|ℓ(x′) + |x|ℓ(y′) + 3
 -(|x| -|x′|)ℓ(x′) -(|x| -|y′|)ℓ(y′)
≤|x|ℓ(x) + |x′| + 3 -2|x| + |x′| + |y′|     (ℓ(x′), ℓ(y′) ≥1)
= |x|ℓ(x) + |x′| + 3 -2|x| + |x| -1         (|x| = |x′| + |y′| + 1)
= |x|ℓ(x) + 2 + |x′| -|x|
≤|x|ℓ(x) + 1                                (|x′| + 1 ≤|x|).
```
∎

**Corollary 2.** `|S[x]| ≤|x| min(d(x), ℓ(x)) + 1` for any balanced sequence x.
Now, the previous lemmata combine into the following main result.

**Theorem 1.** `|D[x]| ≤|x|(min(d(x), ℓ(x)) + 1) + 1` for any balanced sequence x.
*Proof.* By Corollary 1, D[x] ⊆R[x] ∪S[x] and then,

```
|D[x]| ≤|R[x]| + |S[x]| -1       (λ ∈ R[x] and λ ∈ S[x])
≤|x| + 1 + |x| min(d(x), ℓ(x))   (by Corollary 2)
= |x|(min(d(x), ℓ(x)) + 1) + 1.
```
∎

**Remark 4.** Note that the previous upper bound on the cardinal of the decomposition of a balanced sequence is asymptotically tight, because it is achieved
by an infinite number of sequences. As a matter of fact, the decomposition of
a balanced sequence that describes the leftist full binary tree with m edges,
for all even values of m, which has depth m/2 and m/2 + 1 leaves, contains
m^2/8 + m/4 + 1 ≤ m(m/2 + 1) + 1 sequences.

## Section 3 — Embedded Subtrees and Balanced Sequences

Embedded Subtrees and Balanced Sequences
Maximum common embedded subtree [6, problem GT48] is the problem of finding a tree of largest size that can be embedded into two given trees.

**Definition 5.** Let S and T be trees. S is an embedded subtree of T if it can be
obtained from T by a series of edge contractions. A common embedded subtree
of S and T is a tree which is embedded in both S and T . A maximum common
embedded subtree of S and T is a tree of largest size among all common embedded
subtrees of S and T .

**Theorem 2.** A longest common balanced sequence of the balanced sequences of
two trees is the balanced sequence of a maximum common embedded subtree of
the trees.
*Proof.* Contraction of an edge in a tree corresponds to deletion of an edge annotation (one character pair) in the balanced sequence of the tree. A common
embedded subtree with the largest number of edges corresponds to a longest
common balanced sequence of the balanced sequences of the trees.
∎

**Example 5.** A longest common balanced sequence of the balanced sequences for
the trees S and T in Exmp. 4 can be obtained by deleting the edge annotations
highlighted with dashed lines, together with their adjacent characters. The
resulting balanced sequence has `2(14 - 1) = 2(18 - 5) = 2 · 13 = 26`
characters.

```text
s: 0 0 1 0 0 1 0 0 1 0 1 1 1 1 0 0 0 0 1 0 1 1 0 1 1 0 1 1
t: 0 0 1 0 0 0 1 0 1 1 0 1 1 1 0 0 0 1 0 0 0 1 0 0 1 0 1 1 1 0 1 1 1 0 1 1
```

**Remark 5.** The longest common balanced sequence problem is related to the
longest common subsequence problem for sequences with nested edge annotations, which is useful in the comparison of RNA secondary structures [24].
Although the latter problem is NP-hard [25], it consists in finding a longest
common subsequence that preserves all induced edges, and the former problem
is the particular case in which all characters are paired by an edge with some
other character.


## Section 4 — Computing Maximum Common Embedded Subtrees

Computing Maximum Common Embedded Subtrees
The recursive decomposition of balanced sequences, studied in Section 2, into
head, tail, and concatenation of head and tail, is motivated by a natural way
in which the maximum common embedded subtree problem can be divided in
smaller subproblems.

**Lemma 8.** The size of a longest common balanced sequence lcs(s, t) of two balanced sequences s and t is described by the following recurrence:

```
lcs(s, λ) = 0
lcs(λ, t) = 0

lcs(s, t) = max(
    lcs(head(s), head(t)) + lcs(tail(s), tail(t)) + 1,
    lcs(head(s) tail(s), t),
    lcs(s, head(t) tail(t))
)
```

*Proof.* The only common sequence of a balanced sequence and the empty sequence is the empty sequence, which has zero length. Given two nonempty balanced sequences, if the first edge annotation of both sequences belongs to their
longest common balanced sequence, then its size is one plus the sum of the
sizes of the longest common balanced sequence of the heads and of the longest
common balanced sequence of the tails of the two sequences. Otherwise, their
longest common balanced sequence is the longest balanced sequence of one of
the sequences and the result of deleting the first edge annotation in the other
sequence (that is, contracting the first edge in the other tree).
∎

Now, in order to turn the previous recurrence into an efficient dynamic
programming algorithm, a method is needed to map balanced sequences to array
positions. Actually, only those sequences resulting from the decomposition of a
given sequence need to be taken care of.  Recall from Theorem 1 that the
cardinal of the decomposition of a balanced sequence is linear in the size
times the minimum of the depth and the number of leaves of the tree represented
by the sequence. Definition 4 yields a recursive algorithm for enumerating all
sequences in the decomposition of the balanced sequence of a tree, which can be
assigned unique numbers by exploiting the idea of [26] that a procedure for
dynamically maintaining a global dictionary of unique identifiers, allows
partitioning a tree into equivalence classes of restricted subtree isomorphism
in expected time linear in the size of the tree. The equivalent problem of
assigning unique identifiers to balanced sequences can thus be solved in
expected time linear in the cardinal of the decomposition, meaning expected
time linear in the size times the minimum of the depth and the number of
leaves.

**Theorem 3.** The maximum common embedded subtree problem can be solved in
in O(n1n2 min(d1, ℓ1) min(d2, ℓ2)) time, on ordered trees with n1 and n2 nodes,
of depth d1 and d2 and with ℓ1 and ℓ2 leaves, respectively.

*Proof.* Given a balanced sequence s, the unique number code(t) for each sequence
t ∈ decomp(s) is set to either the number already assigned to that sequence
(looking it up in a dictionary), or to the next non-assigned number for the
decomposition (updating, in this case, the dictionary). Now, for each sequence
t ∈ decomp(s), one unsuccessful dictionary lookup of t and one insertion of
⟨t, code(t)⟩in the dictionary are made. With standard hashing techniques, each
such operation takes expected O(1) time and, by Theorem 1, the number of
sequences in the decomposition of the balanced sequence of a tree with m edges,
depth d and ℓleaves is O(m min(d, ℓ)).

Further, the size of a longest common balanced sequence lcs(s, t) of two sequences s and t is found with standard dynamic programming techniques, where
memoization is realized by storing the solution to a subproblem on sequences
x and y at entry a[code(x), code(y)] in an integer array a. The size of a longest
common balanced sequence lcs(s, t) of two sequences s and t is either looked
up at array entry a[code(s), code(t)], or computed according to Lemma 8 and
stored in that array entry. There are, by Theorem 1, O(m1 min(d1, ℓ1)) and
O(m2 min(d2, ℓ2)) sequences in the decomposition of the balanced sequences of
two trees with respectively m1 and m2 edges, depth d1 and d2, and ℓ1 and ℓ2
leaves and, for each pair of sequences, four array accesses and one array update
are made, each taking O(1) time.

The encoding of two trees with m1 and m2 edges takes thus expected O(n1
min(d1, ℓ1) + n2 min(d2, ℓ2)) time upon which, solving the longest common balanced sequence problem takes O(n1n2 min(d1, ℓ1) min(d2, ℓ2)) time.
∎

Maximum common labeled subtrees of labeled trees can be found by a simple and
straightforward extension of the dynamic programming algorithm. Assume, without
loss of generality, that trees have labels on edges. Trees with labels on nodes
can be dealt with by shifting node labels to the edge joining the parent with
the node, for all nonroot nodes.  Now, for each edge annotation in the balanced
sequence of a tree, the edge label can be associated with the corresponding 0
character in the balanced sequence. Then, when computing the size lcs(s, t) of
a largest common balanced sequence of sequences s and t, or when mapping the
first edge annotation in s to the first edge annotation in t, the case
lcs(head(s), head(t))+lcs(tail(s), tail(t))+1 of the recurrence in Lemma 8
applies only if the edge labels associated to these first edge annotations are
identical, or if they satisfy some predefined criteria, depending on the
intended application.
