# Problem Statement: Lollipop Regions

## Object

A lollipop is a plane curve made from:

- one circle of positive radius;
- one half-line attached to the circle at one point and extending radially outward.

Equivalently, choose:

- a center point `C = (x,y)`;
- a radius `r > 0`;
- a unit direction vector `u`.

The lollipop is the union of:

```text
circle: { P : |P - C| = r }
stem:   { C + r*u + t*u : t >= 0 }.
```

The point `C + r*u` is the anchor point where the stem meets the circle.

## Sequence

Let `a(n)` be the maximum number of connected regions into which the plane can be divided by drawing `n` lollipops of arbitrary centers, radii, and directions.

The known initial values are:

```text
a(0) = 1
a(1) = 2
a(2) = 10
a(3) = 25
a(4) = 45
```

Known bounds for the next values are:

```text
71 <= a(5) <= 72
104 <= a(6) <= 106
142 <= a(7) <= 145
186 <= a(8) <= 191
```

## Counting Regions

For a generic connected arrangement of `n` lollipops, let `C(n)` be the total number of crossing points between distinct lollipops. Then:

```text
a(n) = max C(n) + n + 1.
```

So maximizing regions is equivalent to maximizing pairwise crossing points.

## Pairwise Intersection Types

For two lollipops `L_i` and `L_j`, intersections can occur in four ways:

```text
circle_i with circle_j
stem_i   with stem_j
stem_i   with circle_j
stem_j   with circle_i
```

The maximum contributions are:

```text
circle-circle:       at most 2
stem-stem:           at most 1
one stem vs circle:  at most 2
other stem vs circle: at most 2
```

Therefore two lollipops can meet in at most:

```text
2 + 1 + 2 + 2 = 7
```

crossing points.

The naive upper bound is:

```text
C(n) <= 7 * binomial(n,2)
a(n) <= 7 * binomial(n,2) + n + 1
```

This bound is sharp for `n = 0,1,2,3`, but not for `n = 4`.

## Good Pairs

A pair of lollipops is called good if the two lollipops have three or four stem-circle intersections between them.

If two lollipops form a good pair, then the angle between their stem directions is strictly greater than `pi/2`.

It is impossible to choose four directions in the plane such that every pair of directions is separated by an angle strictly greater than `pi/2`. Therefore, the graph whose vertices are lollipops and whose edges are good pairs contains no `K_4`.

By Turan's theorem, the maximum number of good pairs among `n` lollipops is the number of edges in the complete balanced tripartite graph `T(3,n)`.

If:

```text
n = 3m,     good_pairs <= 3m^2
n = 3m + 1, good_pairs <= 3m^2 + 2m
n = 3m + 2, good_pairs <= 3m^2 + 4m + 1
```

then every good pair contributes at most `7` crossings, while every non-good pair contributes at most `5` crossings.

Thus:

```text
C(n) <= 5 * binomial(n,2) + 2 * edges(T(3,n)).
```

For `n = 4`, this gives:

```text
edges(T(3,4)) = 5
C(4) <= 5*6 + 2*5 = 40
a(4) <= 40 + 4 + 1 = 45.
```

A construction with `40` crossings exists, so:

```text
a(4) = 45.
```

For `n = 5`, this gives:

```text
edges(T(3,5)) = 8
C(5) <= 5*10 + 2*8 = 66
a(5) <= 66 + 5 + 1 = 72.
```

A construction with `65` crossings exists, so:

```text
71 <= a(5) <= 72.
```

## Four-Lollipop Optimal Pattern

For `n = 4`, the optimal crossing-count table can be represented as:

```text
      1  2  3  4
1     *  5  7  7
2        *  7  7
3           *  7
4              *
```

The total number of crossings is:

```text
5 + 7 + 7 + 7 + 7 + 7 = 40.
```

Therefore:

```text
R = 40 + 4 + 1 = 45.
```

## Five-Lollipop Bounds

For `n = 5`, the current exact value is not known from the stated results.

The known crossing-count bounds are:

```text
65 <= C(5) <= 66.
```

The corresponding region-count bounds are:

```text
71 <= a(5) <= 72.
```

An equality case at the upper bound would require:

```text
total crossings = 66
good pairs = 8
non-good pairs = 2
each good pair has 7 crossings
each non-good pair has 5 crossings
```

After relabeling, the two non-good pairs may be taken to be:

```text
(0,1) and (3,4).
```

The required pair-count table is:

```text
      0  1  2  3  4
0     *  5  7  7  7
1        *  7  7  7
2           *  7  7
3              *  5
4                 *
```

For a 66-crossing equality case, the component states are forced as follows.

Every pair must have:

```text
circle-circle intersections = 2
stem-stem intersections = 1
```

Every good pair must have:

```text
stem_i with circle_j = 2
stem_j with circle_i = 2
```

Each non-good pair must have exactly two directed stem-circle intersections in total.

If two stems intersect, it is impossible for both directed stem-circle counts to equal one. To see this, let the stems intersect at `X`, let `a` and `b` be the distances from the two anchors to `X`, let `s` be the second radius, and let `c` be the cosine of the angle between the two stem directions. If the first anchor lies inside the second circle, then:

```text
a^2 + b^2 + 2bs < 2a(b+s)c.
```

Since `c <= 1`, this implies:

```text
(a-b)^2 < 2s(a-b),
```

so:

```text
a > b.
```

The symmetric condition for the second anchor inside the first circle implies:

```text
b > a.
```

Both cannot hold. Therefore the balanced split `(1,1)` cannot occur on a deficient edge whose stems intersect.

Thus each non-good pair in a 66-crossing equality case must be one-sided:

```text
(stem_i with circle_j, stem_j with circle_i) = (2,0)
```

or:

```text
(stem_i with circle_j, stem_j with circle_i) = (0,2).
```

The two non-good pairs must have stem-direction angle strictly less than `pi/2`.

If a non-good pair had angle greater than `pi/2`, then that pair together with the singleton lollipop and either lollipop from the other non-good pair would give four stem directions whose six pairwise angles are all greater than `pi/2`, which is impossible in the plane. If the angle were exactly `pi/2`, then neither stem line could intersect the other circle twice because the distance from the other circle center to the perpendicular stem line is larger than the circle radius. Since each non-good pair has one directed double stem-circle intersection, equality at `pi/2` is also impossible.

There is also a forced distance order on an acute one-sided non-good pair.

Let two stems meet at `X`. Let:

```text
a = distance from anchor i to X
b = distance from anchor j to X
s = radius of lollipop j
phi = acute angle between the stems
c = cos(phi)
h = sin(phi)
```

If stem `i` intersects circle `j` twice, then the center of circle `j` is at distance `b+s` from `X` along stem `j`. For the line of stem `i` to meet circle `j`:

```text
(b+s)h < s.
```

Since `h^2 = 1-c^2`, this implies:

```text
c > sqrt(b^2 + 2bs)/(b+s).
```

For both intersections to lie on the forward ray of stem `i`, the anchor of lollipop `i` must lie before the nearer intersection point. In particular:

```text
a > (b+s)c.
```

If `a <= b`, then this would force:

```text
c < b/(b+s).
```

But:

```text
sqrt(b^2 + 2bs) > b.
```

So the two inequalities on `c` cannot both hold. Therefore:

```text
if stem i intersects circle j twice in an acute one-sided pair, then a > b.
```

In an upper-bound equality case, each non-good pair is acute and one-sided. Therefore, on each non-good pair, the lollipop whose stem supplies the two stem-circle intersections must have the anchor farther from the stem-stem crossing.

Because the two non-good pairs are disjoint, labels can be swapped within each non-good pair. Thus, after relabeling, the only directed case that has to be considered is:

```text
(0,1) has state (2,1,2,0)
(3,4) has state (2,1,2,0)
```

with the corresponding anchor-distance inequalities:

```text
on pair (0,1): anchor 0 is farther from the stem-stem crossing than anchor 1
on pair (3,4): anchor 3 is farther from the stem-stem crossing than anchor 4
```

## General Lower-Bound Construction From Four Lollipops

Start with the optimal four-lollipop crossing table:

```text
      1  2  3  4
1     *  5  7  7
2        *  7  7
3           *  7
4              *
```

Replace lollipop `i` by a small cluster of `m_i` nearby perturbed copies. In this construction:

- crossings between different clusters use the table entries above;
- crossings within the same cluster contribute `4` per pair.

For total `n = m_1 + m_2 + m_3 + m_4`, the crossing count is:

```text
C =
5*m_1*m_2
+ 7*m_1*m_3
+ 7*m_1*m_4
+ 7*m_2*m_3
+ 7*m_2*m_4
+ 7*m_3*m_4
+ 4*sum_i binomial(m_i,2).
```

For `n = 5`, choosing:

```text
(m_1,m_2,m_3,m_4) = (1,1,1,2)
```

gives:

```text
C = 65
a(5) >= 65 + 5 + 1 = 71.
```

For `n = 6`, choosing:

```text
(m_1,m_2,m_3,m_4) = (1,1,2,2)
```

gives:

```text
C = 97
a(6) >= 97 + 6 + 1 = 104.
```

For `n = 7`, choosing:

```text
(m_1,m_2,m_3,m_4) = (1,2,2,2)
```

gives:

```text
C = 134
a(7) >= 134 + 7 + 1 = 142.
```

For `n = 8`, choosing:

```text
(m_1,m_2,m_3,m_4) = (1,2,2,3)
```

gives:

```text
C = 177
a(8) >= 177 + 8 + 1 = 186.
```
