pub enum IndentedText {
    Line(String),
    LineStr(&'static str),
    AddToLastLine(String),
    Many(Vec<IndentedText>),
    Indent(Vec<IndentedText>),
    Empty,
}

use IndentedText::*;

impl IndentedText {
    pub fn line(text: String) -> Self {
        Line(text)
    }

    pub fn line_str(text: &'static str) -> Self {
        LineStr(text)
    }

    pub fn many_vec(nodes: Vec<IndentedText>) -> Self {
        Many(nodes)
    }

    pub fn many(nodes: impl IntoIterator<Item = Self>) -> Self {
        nodes.into_iter().reduce(Self::then).unwrap_or(Empty)
    }

    pub fn lines(lines: impl Iterator<Item = String>) -> Self {
        Many(lines.map(Line).collect())
    }

    pub fn indent(self) -> Self {
        match self {
            Many(nodes) => Indent(nodes),
            Empty => Empty,
            root => Indent(vec![root]),
        }
    }

    pub fn then(self, other: IndentedText) -> Self {
        match (self, other) {
            (Empty, other) | (other, Empty) => other,
            (Many(mut nodes), Many(other_nodes)) => {
                nodes.extend(other_nodes);
                Many(nodes)
            }
            (Many(mut nodes), other) => {
                nodes.push(other);
                Many(nodes)
            }
            (root, Many(mut nodes)) => {
                nodes.insert(0, root);
                Many(nodes)
            }
            (root, other) => Many(vec![root, other]),
        }
    }

    pub fn to_string(&self) -> String {
        let mut code = String::new();
        self.to_string_impl(&mut code, 0);
        code
    }

    /// Write the indented text to the given string, with the given indentation level.
    fn to_string_impl(&self, code: &mut String, indent: usize) {
        match self {
            Line(line) => {
                code.push_str(&"    ".repeat(indent));
                code.push_str(line);
                code.push('\n');
            }
            LineStr(line) => {
                code.push_str(&"    ".repeat(indent));
                code.push_str(line);
                code.push('\n');
            }
            AddToLastLine(text) => {
                code.pop();
                code.push_str(text);
                code.push('\n')
            }
            Many(nodes) => {
                for node in nodes {
                    node.to_string_impl(code, indent);
                }
            }
            Indent(nodes) => {
                for node in nodes {
                    node.to_string_impl(code, indent + 1);
                }
            }
            Empty => (),
        }
    }
}
