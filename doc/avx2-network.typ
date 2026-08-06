#set page(paper: "a4", margin: (x: 2.4cm, y: 2.4cm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)

#align(center)[
  #text(size: 15pt)[*The network djbsort's AVX2 sort runs, at 64 lines*]

  #v(0.3em)
  #text(size: 10pt)[Laurent Théry]
]

#v(0.6em)

A connector joins two lines; the minimum leaves on the upper one.

#v(0.4em)
#align(center)[
  #box(width: 120pt, height: 34pt, {
    place(dx: 0pt, dy: 6pt, line(length: 120pt, stroke: 0.8pt))
    place(dx: 0pt, dy: 26pt, line(length: 120pt, stroke: 0.8pt))
    place(dx: 60pt, dy: 6pt, line(end: (0pt, 20pt), stroke: 0.8pt))
    place(dx: 58.5pt, dy: 4.5pt, circle(radius: 1.5pt, fill: black, stroke: none))
    place(dx: 58.5pt, dy: 24.5pt, circle(radius: 1.5pt, fill: black, stroke: none))
    place(dx: 124pt, dy: 0pt, text(size: 8pt)[$min$])
    place(dx: 124pt, dy: 20pt, text(size: 8pt)[$max$])
  })
]

#v(0.6em)

At 64 lines the sort performs 656 comparisons, in 82 groups of eight done at
once by one vector instruction. Drawn one comparison at a time the picture is
unreadable, so each box below stands for a whole component, and its arrow points towards the larger values.

The shape is a bitonic sort. First every group of four lines is sorted, the
upper four decreasing and the lower four increasing, so every group of eight
falls and then rises. Then merges of doubling size, each turning two
neighbouring runs of opposite direction into one.

#v(0.8em)

#let gap = 4.6pt
#let boxfor(x, w, a, c, down) = {
  place(dx: x, dy: gap * a - 3pt,
    rect(width: w, height: gap * (c - 1) + 6pt, radius: 1.5pt,
         stroke: 0.5pt + luma(60), fill: luma(246)))
  place(dx: x, dy: gap * a + gap * (c - 1) / 2 - 4.5pt,
    box(width: w, align(center, text(size: 7.5pt)[#if down [$arrow.t$] else [$arrow.b$]])))
}

#align(center)[
#box(width: 350pt, height: gap * 63 + 16pt, {
  // the 64 lines
  for i in range(64) {
    place(dx: 0pt, dy: gap * i, line(length: 350pt, stroke: 0.3pt + luma(140)))
  }
  // sort each half-block of four: lower four down, upper four up
  for j in range(8) {
    boxfor(14pt, 46pt, 8 * j, 4, true)
    boxfor(14pt, 46pt, 8 * j + 4, 4, false)
  }
  // merge 8, merge 16, merge 32, merge 64; directions alternate
  for j in range(8) { boxfor(84pt, 54pt, 8 * j, 8, calc.even(j)) }
  for j in range(4) { boxfor(152pt, 54pt, 16 * j, 16, calc.even(j)) }
  for j in range(2) { boxfor(220pt, 54pt, 32 * j, 32, calc.even(j)) }
  boxfor(288pt, 54pt, 0, 64, false)
})
]

#v(0.2em)

#align(center)[
  #box(width: 350pt, {
    grid(columns: (68pt, 68pt, 68pt, 68pt, 68pt), align: center,
      text(size: 8pt)[sort 4], text(size: 8pt)[merge 8],
      text(size: 8pt)[merge 16], text(size: 8pt)[merge 32],
      text(size: 8pt)[merge 64])
  })
]

#v(1em)

= What the boxes contain

*sort 4* is the five-comparison network on four lines, at distances
$1, 1, 2, 2, 1$. A bitonic sort of four would use six, so this is where the
code is smaller than a plain bitonic sorter.

#v(0.4em)
#align(center)[
  #box(width: 150pt, height: 3 * 20pt + 14pt, {
    for i in range(4) {
      place(dx: 0pt, dy: 6pt + 20pt * i, line(length: 150pt, stroke: 0.8pt))
    }
    let cx = (20pt, 20pt, 55pt, 90pt, 125pt)
    let ca = (0, 2, 0, 1, 1)
    let cb = (1, 3, 2, 3, 2)
    for i in range(5) {
      place(dx: cx.at(i), dy: 6pt + 20pt * ca.at(i),
            line(end: (0pt, 20pt * (cb.at(i) - ca.at(i))), stroke: 0.8pt))
      place(dx: cx.at(i) - 1.5pt, dy: 4.5pt + 20pt * ca.at(i),
            circle(radius: 1.5pt, fill: black, stroke: none))
      place(dx: cx.at(i) - 1.5pt, dy: 4.5pt + 20pt * cb.at(i),
            circle(radius: 1.5pt, fill: black, stroke: none))
    }
  })
]

*merge $2 m$* takes a run down followed by a run up and returns one sorted
run. It is the usual cascade: compare at distance $m$, then $m slash 2$, down
to $1$. At 64 lines the merges use distances $4, 2, 1$ then $8, 4, 2, 1$ then
$16, 8, 4, 2, 1$ then $32, 16, 8, 4, 2, 1$ --- which is what the code
performs, once its comparisons are named by the array position each value
ends in.

#v(0.4em)
#align(center)[
  #box(width: 190pt, height: 7 * 14pt + 14pt, {
    for i in range(8) {
      place(dx: 0pt, dy: 6pt + 14pt * i, line(length: 190pt, stroke: 0.8pt))
    }
    let cols = ((0, 4), (1, 5), (2, 6), (3, 7),
                (0, 2), (1, 3), (4, 6), (5, 7),
                (0, 1), (2, 3), (4, 5), (6, 7))
    let xs = (18pt, 26pt, 34pt, 42pt, 80pt, 88pt, 96pt, 104pt,
              140pt, 148pt, 156pt, 164pt)
    for i in range(12) {
      let a = cols.at(i).at(0)
      let b = cols.at(i).at(1)
      place(dx: xs.at(i), dy: 6pt + 14pt * a,
            line(end: (0pt, 14pt * (b - a)), stroke: 0.8pt))
      place(dx: xs.at(i) - 1.5pt, dy: 4.5pt + 14pt * a,
            circle(radius: 1.5pt, fill: black, stroke: none))
      place(dx: xs.at(i) - 1.5pt, dy: 4.5pt + 14pt * b,
            circle(radius: 1.5pt, fill: black, stroke: none))
    }
  })
]

= Where the eight-at-a-time grouping sits

One vector instruction performs eight comparisons at once. They are always
eight copies of the same comparison, placed regularly across the array, so a
single instruction is a connector in its own right --- its eight comparisons
are on sixteen distinct lines. Here are four of the eighty-two, on all 64
lines.

#v(0.6em)

#let gp = 2.9pt
#let onebatch(ps, label) = {
  block[
    #box(width: 96pt, height: gp * 63 + 10pt, {
      for i in range(64) {
        place(dx: 0pt, dy: gp * i, line(length: 96pt, stroke: 0.25pt + luma(170)))
      }
      let xs = (10pt, 21pt, 32pt, 43pt, 54pt, 65pt, 76pt, 87pt)
      for i in range(8) {
        let a = ps.at(i).at(0)
        let b = ps.at(i).at(1)
        place(dx: xs.at(i), dy: gp * a,
              line(end: (0pt, gp * (b - a)), stroke: 0.7pt))
        place(dx: xs.at(i) - 1.3pt, dy: gp * a - 1.3pt,
              circle(radius: 1.3pt, fill: black, stroke: none))
        place(dx: xs.at(i) - 1.3pt, dy: gp * b - 1.3pt,
              circle(radius: 1.3pt, fill: black, stroke: none))
      }
    })
    #v(0.2em)
    #align(center)[#text(size: 7.5pt)[#label]]
  ]
}

#align(center)[
  #grid(columns: (104pt, 104pt, 104pt, 104pt), column-gutter: 4pt,
    onebatch(((0,1),(8,9),(16,17),(24,25),(32,33),(40,41),(48,49),(56,57)),
             [no. 1, distance 1]),
    onebatch(((0,4),(8,12),(16,20),(24,28),(32,36),(40,44),(48,52),(56,60)),
             [no. 11, distance 4]),
    onebatch(((0,8),(4,12),(16,24),(20,28),(32,40),(36,44),(48,56),(52,60)),
             [no. 23, distance 8]),
    onebatch(((0,32),(1,33),(2,34),(3,35),(4,36),(5,37),(6,38),(7,39)),
             [no. 59, distance 32]))
]

#v(0.6em)

The comparisons of one instruction are eight lines apart in most stages, and
next to each other in the stage that follows the transpose. That is what the
transposes are for: they change which sixteen lines sit together in the
registers, so that the next distance can again be handled eight at a time.

The whole sort is 82 such instructions, and the picture on the first page is
what they add up to.
