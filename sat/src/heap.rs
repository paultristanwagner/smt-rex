//! Indexed binary max-heap of variables ordered by an activity array the solver owns (VSIDS),
//! so a bump is one array write plus a sift-up.

use smtrex_core::Var;

#[derive(Default)]
pub struct VarHeap {
    heap: Vec<Var>,
    /// `pos[v]` = index of `v` in `heap`, or `usize::MAX` if absent.
    pos: Vec<usize>,
}

const ABSENT: usize = usize::MAX;

impl VarHeap {
    pub fn ensure_var(&mut self, v: Var) {
        if v.index() >= self.pos.len() {
            self.pos.resize(v.index() + 1, ABSENT);
        }
    }

    pub fn contains(&self, v: Var) -> bool {
        v.index() < self.pos.len() && self.pos[v.index()] != ABSENT
    }

    #[inline]
    fn lt(&self, act: &[f64], a: Var, b: Var) -> bool {
        act[a.index()] < act[b.index()]
    }

    fn sift_up(&mut self, act: &[f64], mut i: usize) {
        let x = self.heap[i];
        while i > 0 {
            let parent = (i - 1) >> 1;
            if !self.lt(act, self.heap[parent], x) {
                break;
            }
            self.heap[i] = self.heap[parent];
            self.pos[self.heap[i].index()] = i;
            i = parent;
        }
        self.heap[i] = x;
        self.pos[x.index()] = i;
    }

    fn sift_down(&mut self, act: &[f64], mut i: usize) {
        let x = self.heap[i];
        let n = self.heap.len();
        loop {
            let mut child = 2 * i + 1;
            if child >= n {
                break;
            }
            if child + 1 < n && self.lt(act, self.heap[child], self.heap[child + 1]) {
                child += 1;
            }
            if !self.lt(act, x, self.heap[child]) {
                break;
            }
            self.heap[i] = self.heap[child];
            self.pos[self.heap[i].index()] = i;
            i = child;
        }
        self.heap[i] = x;
        self.pos[x.index()] = i;
    }

    /// Insert `v` if absent.
    pub fn insert(&mut self, act: &[f64], v: Var) {
        self.ensure_var(v);
        if self.contains(v) {
            return;
        }
        let i = self.heap.len();
        self.heap.push(v);
        self.pos[v.index()] = i;
        self.sift_up(act, i);
    }

    /// Restore the heap property after `v`'s activity increased.
    pub fn increase(&mut self, act: &[f64], v: Var) {
        if self.contains(v) {
            let i = self.pos[v.index()];
            self.sift_up(act, i);
        }
    }

    /// Remove and return the maximum-activity variable.
    pub fn pop_max(&mut self, act: &[f64]) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        self.pos[top.index()] = ABSENT;
        let last = self.heap.pop().unwrap();
        if !self.heap.is_empty() && last != top {
            self.heap[0] = last;
            self.pos[last.index()] = 0;
            self.sift_down(act, 0);
        }
        Some(top)
    }
}
