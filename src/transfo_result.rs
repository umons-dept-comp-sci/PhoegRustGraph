use Set;

const PRESENT: u8 = 0b1;
const ABSENT: u8 = 0b0;
const CHANGED: u8 = 0b10;
const ADDED: u8 = PRESENT + CHANGED;
const REMOVED: u8 = ABSENT + CHANGED;

pub struct GraphTransformation {
    n: u64,
    m: u64,
    data: Vec<Set>,
}

impl GraphTransformation {
    pub fn new(n: u64) -> GraphTransformation {
        let mut v = Vec::with_capacity(n as usize);
        let mut s;
        for i in 0..n {
            s = Set::new(2 * n);
            s.add(2 * i);
            v.push(s);
        }
        GraphTransformation {
            n: n,
            m: 0,
            data: v,
        }
    }

    pub fn order(&self) -> u64 {
        self.n
    }

    pub fn size(&self) -> u64 {
        self.m
    }

    pub fn is_edge_modified(&self, i: u64, j: u64) -> bool {
        self.data[i as usize].contains(2 * j)
    }

    pub fn is_edge(&self, i: u64, j: u64) -> bool {
        self.data[i as usize].contains(2 * j + 1)
    }

    pub fn is_vertex_modified(&self, i: u64) -> bool {
        self.data[i as usize].contains(2 * i)
    }

    pub fn is_vertex(&self, i: u64) -> bool {
        self.data[i as usize].contains(2 * i + 1)
    }

    pub fn add_edge(&mut self, i: u64, j: u64) {
        if !self.is_edge(i, j) {
            self.data[i as usize].add(2 * j + 1);
            self.data[i as usize].flip(2 * j);
            self.data[j as usize].add(2 * i + 1);
            self.data[j as usize].flip(2 * i);
        }
    }

    pub fn remove_edge(&mut self, i: u64, j: u64) {
        if self.is_edge(i, j) {
            self.data[i as usize].remove(2 * j + 1);
            self.data[i as usize].flip(2 * j);
            self.data[j as usize].remove(2 * i + 1);
            self.data[j as usize].flip(2 * i);
        }
    }

    pub fn add_vertex(&mut self, i: u64) {
        if i >= self.n {
            let max = if self.data.len() > 0 {
                self.data[0].getmax() + 1
            } else {
                0
            };
            for i in 0..self.n {
                self.data[i as usize].setmax(max);
            }
            let mut new_set = Set::new(max);
            new_set.add(2 * self.n);
            new_set.add(2 * self.n + 1);
            self.data.push(Set::new(max));
            self.n += 1;
        } else if !self.is_vertex(i) {
            self.data[i as usize].add(2*i+1);
            self.data[i as usize].flip(2*i);
        }
    }

    pub fn remove_vertex(&mut self, i: u64) {
        if self.is_vertex(i) {
            self.data[i as usize].remove(2*i+1);
            self.data[i as usize].flip(2*i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flags() {}
}
