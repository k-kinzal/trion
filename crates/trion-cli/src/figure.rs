//! Figures of diagrams: a layered graph drawn as inline SVG, with no script.

use crate::doc::esc;

#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Shape {
    Box,
    Step,
    Choice,
    Start,
    Finish,
}

struct Node {
    name: String,
    detail: Vec<String>,
    shape: Shape,
}

#[derive(Default)]
pub(crate) struct Graph {
    nodes: Vec<Node>,
    edges: Vec<(usize, usize, String)>,
}

/// Splits `zero or more normative statements` into its cardinality and its type.
pub(crate) fn cardinality(target: &str) -> (String, String) {
    let words: Vec<&str> = target.split_whitespace().collect();
    let take = match words.as_slice() {
        ["zero" | "one", "or", "more", ..] => 3,
        ["exactly" | "at", ..] if words.len() > 2 => {
            if words[0] == "at" { 3 } else { 2 }
        }
        ["a" | "an" | "one" | "some" | "each" | "every" | "no", ..] => 1,
        _ => 0,
    };
    (words[..take].join(" "), words[take..].join(" "))
}

/// The singular of a type name, so that `statements` and `statement` are one node.
pub(crate) fn singular(name: &str) -> String {
    let name = name.trim();
    match name.strip_suffix('s') {
        Some(stem) if !stem.ends_with('s') && !stem.ends_with('u') && !stem.ends_with('i') && stem.len() > 2 => stem.to_string(),
        _ => name.to_string(),
    }
}

/// Breaks a text into lines of about `width` characters.
fn wrap(text: &str, width: usize) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    for word in text.split_whitespace() {
        match lines.last_mut() {
            Some(line) if line.len() + 1 + word.len() <= width => {
                line.push(' ');
                line.push_str(word);
            }
            _ => lines.push(word.to_string()),
        }
    }
    lines
}

const CHAR: f64 = 6.6;
const ROW: f64 = 16.0;

impl Graph {
    /// The node of this name, added when it is new.
    pub(crate) fn node(&mut self, name: &str, shape: Shape) -> usize {
        if let Some(found) = self.nodes.iter().position(|n| n.name == name && (n.shape == shape || matches!(shape, Shape::Box | Shape::Step))) {
            return found;
        }
        self.nodes.push(Node { name: name.to_string(), detail: Vec::new(), shape });
        self.nodes.len() - 1
    }

    pub(crate) fn describe(&mut self, node: usize, text: &str) {
        self.nodes[node].detail = wrap(text, 34);
    }

    pub(crate) fn edge(&mut self, from: usize, to: usize, label: &str) {
        self.edges.push((from, to, label.trim().to_string()));
    }

    fn size(&self, node: &Node) -> (f64, f64) {
        match node.shape {
            Shape::Start => (16.0, 16.0),
            Shape::Finish => (22.0, 22.0),
            Shape::Choice => (node.name.len() as f64 * CHAR + 56.0, 40.0),
            _ => {
                let widest = node.detail.iter().map(String::len).chain([node.name.len()]).max().unwrap_or(0);
                ((widest as f64 * CHAR + 26.0).max(72.0), (1 + node.detail.len()) as f64 * ROW + 16.0)
            }
        }
    }

    /// The layer of each node: one more than the deepest node that leads to
    /// it, with the edges that close a cycle left out.
    fn layers(&self) -> Vec<usize> {
        let n = self.nodes.len();
        let mut state = vec![0u8; n];
        let mut back = vec![false; self.edges.len()];
        fn visit(graph: &Graph, at: usize, state: &mut [u8], back: &mut [bool]) {
            state[at] = 1;
            for (index, (from, to, _)) in graph.edges.iter().enumerate() {
                if *from != at {
                    continue;
                }
                match state[*to] {
                    0 => visit(graph, *to, state, back),
                    1 => back[index] = true,
                    _ => {}
                }
            }
            state[at] = 2;
        }
        for at in 0..n {
            if state[at] == 0 {
                visit(self, at, &mut state, &mut back);
            }
        }
        let mut layer = vec![0usize; n];
        for _ in 0..n {
            for (index, (from, to, _)) in self.edges.iter().enumerate() {
                if !back[index] && from != to && layer[*to] < layer[*from] + 1 {
                    layer[*to] = layer[*from] + 1;
                }
            }
        }
        layer
    }

    /// The graph as an SVG element. `id` keeps the marker of each figure apart.
    pub(crate) fn svg(&self, id: usize, label: &str) -> String {
        if self.nodes.is_empty() {
            return String::new();
        }
        let layer = self.layers();
        let depth = layer.iter().copied().max().unwrap_or(0) + 1;
        let sizes: Vec<(f64, f64)> = self.nodes.iter().map(|n| self.size(n)).collect();
        let gap_x = 46.0;
        let gap_y = 54.0;
        let mut rows: Vec<Vec<usize>> = vec![Vec::new(); depth];
        for (index, at) in layer.iter().enumerate() {
            rows[*at].push(index);
        }
        let row_width = |row: &Vec<usize>| row.iter().map(|&i| sizes[i].0).sum::<f64>() + gap_x * row.len().saturating_sub(1) as f64;
        // Room on both sides for the edges that go around.
        let margin = 70.0;
        let width = rows.iter().map(row_width).fold(0.0, f64::max) + 2.0 * margin;
        let mut center = vec![(0.0, 0.0); self.nodes.len()];
        let mut y = 14.0;
        for row in &rows {
            let height = row.iter().map(|&i| sizes[i].1).fold(0.0, f64::max);
            let mut x = (width - row_width(row)) / 2.0;
            for &i in row {
                center[i] = (x + sizes[i].0 / 2.0, y + height / 2.0);
                x += sizes[i].0 + gap_x;
            }
            y += height + gap_y;
        }
        let height = y - gap_y + 14.0;
        let mut out = format!(
            "<svg xmlns=\"http://www.w3.org/2000/svg\" role=\"img\" aria-label=\"{}\" width=\"{width:.0}\" height=\"{height:.0}\" viewBox=\"0 0 {width:.0} {height:.0}\">\n<defs><marker id=\"arrow{id}\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M0,0 L10,5 L0,10 z\" fill=\"currentColor\"/></marker></defs>\n",
            esc(label)
        );
        let mut labels = String::new();
        let mut used: Vec<(usize, usize)> = Vec::new();
        for (from, to, text) in &self.edges {
            let (ax, ay) = center[*from];
            let (bx, by) = center[*to];
            let (aw, ah) = sizes[*from];
            let (bw, bh) = sizes[*to];
            let repeat = used.iter().filter(|pair| **pair == (*from, *to) || **pair == (*to, *from)).count() as f64;
            used.push((*from, *to));
            let (path, lx, ly) = if from == to {
                let (x, y) = (ax + aw / 2.0, ay);
                (format!("M{x:.1},{:.1} C{:.1},{:.1} {:.1},{:.1} {x:.1},{:.1}", y - 8.0, x + 44.0, y - 26.0, x + 44.0, y + 26.0, y + 8.0), x + 40.0, y - 26.0 - repeat * 13.0)
            } else if layer[*to] > layer[*from] {
                let shift = repeat * 18.0;
                let (x1, y1, x2, y2) = (ax + shift, ay + ah / 2.0, bx + shift, by - bh / 2.0);
                // The label sits nearer the target, clear of the edges that leave the same node.
                (format!("M{x1:.1},{y1:.1} L{x2:.1},{y2:.1}"), x1 + (x2 - x1) * 0.62, y1 + (y2 - y1) * 0.62 + 4.0)
            } else {
                // An edge to the same layer or back up goes around on the right.
                let (x1, y1, x2, y2) = (ax + aw / 2.0, ay, bx + bw / 2.0, by);
                let reach = x1.max(x2) + 40.0 + repeat * 16.0;
                (format!("M{x1:.1},{y1:.1} C{reach:.1},{y1:.1} {reach:.1},{y2:.1} {x2:.1},{y2:.1}"), reach - 12.0, (y1 + y2) / 2.0 + 4.0)
            };
            out.push_str(&format!("<path class=\"wire\" d=\"{path}\" marker-end=\"url(#arrow{id})\"/>\n"));
            if !text.is_empty() {
                labels.push_str(&format!("<text class=\"edge\" x=\"{lx:.1}\" y=\"{ly:.1}\" text-anchor=\"middle\">{}</text>\n", esc(text)));
            }
        }
        for (index, node) in self.nodes.iter().enumerate() {
            let (cx, cy) = center[index];
            let (w, h) = sizes[index];
            match node.shape {
                Shape::Start => out.push_str(&format!("<circle class=\"dot\" cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"7\"/>\n")),
                Shape::Finish => out.push_str(&format!("<circle class=\"ring\" cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"10\"/><circle class=\"dot\" cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"6\"/>\n")),
                Shape::Choice => {
                    out.push_str(&format!("<polygon class=\"shape\" points=\"{:.1},{cy:.1} {cx:.1},{:.1} {:.1},{cy:.1} {cx:.1},{:.1}\"/>\n", cx - w / 2.0, cy - h / 2.0, cx + w / 2.0, cy + h / 2.0));
                    out.push_str(&format!("<text x=\"{cx:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>\n", cy + 4.0, esc(&node.name)));
                }
                Shape::Box | Shape::Step => {
                    let radius = if node.shape == Shape::Step { 10 } else { 2 };
                    out.push_str(&format!("<rect class=\"shape\" x=\"{:.1}\" y=\"{:.1}\" width=\"{w:.1}\" height=\"{h:.1}\" rx=\"{radius}\"/>\n", cx - w / 2.0, cy - h / 2.0));
                    let top = cy - h / 2.0 + 8.0 + ROW - 4.0;
                    out.push_str(&format!("<text class=\"name\" x=\"{cx:.1}\" y=\"{top:.1}\" text-anchor=\"middle\">{}</text>\n", esc(&node.name)));
                    for (row, line) in node.detail.iter().enumerate() {
                        out.push_str(&format!("<text x=\"{cx:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>\n", top + (row + 1) as f64 * ROW, esc(line)));
                    }
                }
            }
        }
        out.push_str(&labels);
        out.push_str("</svg>");
        out
    }
}
