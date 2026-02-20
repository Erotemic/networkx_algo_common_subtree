use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyList, PyString, PyTuple};
use rustc_hash::FxHashMap as HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, Default)]
struct MatchResult {
    val: f64,
    s1: Vec<u32>,
    s2: Vec<u32>,
}

#[derive(Clone, Debug, Default)]
struct IsoResult {
    any: MatchResult,
    lvl: MatchResult,
}

#[derive(Clone, Debug)]
struct Decomp {
    a: u32,
    b: u32,
    head: u32,
    tail: u32,
    head_tail: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct IndexRange {
    start: u32,
    end: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct StateKey {
    len: u32,
    ranges: Vec<IndexRange>,
}

impl StateKey {
    fn empty() -> Self {
        Self {
            len: 0,
            ranges: Vec::new(),
        }
    }

    fn full(len: usize) -> Self {
        if len == 0 {
            return Self::empty();
        }
        Self {
            len: len as u32,
            ranges: vec![IndexRange {
                start: 0,
                end: len as u32,
            }],
        }
    }
}

struct StatePool {
    states: Vec<StateKey>,
    index: HashMap<StateKey, u32>,
}

impl StatePool {
    fn with_capacity(cap: usize) -> Self {
        Self {
            states: Vec::with_capacity(cap),
            index: HashMap::with_capacity_and_hasher(cap, Default::default()),
        }
    }

    fn intern(&mut self, state: Vec<u32>) -> u32 {
        let mut ranges = Vec::<IndexRange>::new();
        let mut len = 0u32;
        for idx in state {
            len += 1;
            if let Some(last) = ranges.last_mut() {
                if last.end == idx {
                    last.end += 1;
                    continue;
                }
            }
            ranges.push(IndexRange {
                start: idx,
                end: idx + 1,
            });
        }
        self.intern_key(StateKey { len, ranges })
    }

    fn intern_key(&mut self, state: StateKey) -> u32 {
        if let Some(&sid) = self.index.get(&state) {
            return sid;
        }
        let sid = self.states.len() as u32;
        self.index.insert(state.clone(), sid);
        self.states.push(state);
        sid
    }

    fn get(&self, sid: u32) -> &StateKey {
        &self.states[sid as usize]
    }

    #[inline]
    fn is_empty(&self, sid: u32) -> bool {
        self.get(sid).len == 0
    }

    fn first(&self, sid: u32) -> Option<u32> {
        self.get(sid).ranges.first().map(|r| r.start)
    }

    fn index_at_pos(&self, sid: u32, pos: u32) -> Option<u32> {
        let state = self.get(sid);
        if pos >= state.len {
            return None;
        }
        let mut cursor = 0u32;
        for r in &state.ranges {
            let span = r.end - r.start;
            if pos < cursor + span {
                return Some(r.start + (pos - cursor));
            }
            cursor += span;
        }
        None
    }

    fn slice_by_pos(&self, sid: u32, start_pos: u32, end_pos: u32) -> StateKey {
        let state = self.get(sid);
        if start_pos >= end_pos || start_pos >= state.len {
            return StateKey::empty();
        }
        let end_pos = end_pos.min(state.len);
        let mut out = Vec::<IndexRange>::new();
        let mut cursor = 0u32;
        for r in &state.ranges {
            let span = r.end - r.start;
            let seg_start = cursor;
            let seg_end = cursor + span;
            if seg_end <= start_pos {
                cursor = seg_end;
                continue;
            }
            if seg_start >= end_pos {
                break;
            }
            let local_start = start_pos.saturating_sub(seg_start);
            let local_end = (end_pos - seg_start).min(span);
            let start = r.start + local_start;
            let end = r.start + local_end;
            if start < end {
                if let Some(last) = out.last_mut() {
                    if last.end == start {
                        last.end = end;
                    } else {
                        out.push(IndexRange { start, end });
                    }
                } else {
                    out.push(IndexRange { start, end });
                }
            }
            cursor = seg_end;
        }
        StateKey {
            len: end_pos - start_pos,
            ranges: out,
        }
    }

    fn concat(&self, left: &StateKey, right: &StateKey) -> StateKey {
        if left.len == 0 {
            return right.clone();
        }
        if right.len == 0 {
            return left.clone();
        }
        let mut ranges = Vec::with_capacity(left.ranges.len() + right.ranges.len());
        ranges.extend_from_slice(&left.ranges);
        for &r in &right.ranges {
            if let Some(last) = ranges.last_mut() {
                if last.end == r.start {
                    last.end = r.end;
                    continue;
                }
            }
            ranges.push(r);
        }
        StateKey {
            len: left.len + right.len,
            ranges,
        }
    }
}

struct Interner<'py> {
    py: Python<'py>,
    next_id: u32,
    by_hash: HashMap<isize, Vec<(Py<PyAny>, u32)>>,
}

impl<'py> Interner<'py> {
    fn new(py: Python<'py>) -> Self {
        Self {
            py,
            next_id: 0,
            by_hash: HashMap::default(),
        }
    }

    fn id_for(&mut self, obj: &Bound<'py, PyAny>) -> PyResult<u32> {
        let h = obj.hash()?;
        if let Some(bucket) = self.by_hash.get(&h) {
            for (existing, eid) in bucket {
                if existing.bind(self.py).eq(obj.clone())? {
                    return Ok(*eid);
                }
            }
        }
        let new_id = self.next_id;
        self.next_id += 1;
        self.by_hash
            .entry(h)
            .or_default()
            .push((obj.clone().unbind(), new_id));
        Ok(new_id)
    }
}

struct Solver<'py> {
    py: Python<'py>,
    seq1_obj: Bound<'py, PyAny>,
    seq2_obj: Bound<'py, PyAny>,
    seq1_py: Vec<Py<PyAny>>,
    seq2_py: Vec<Py<PyAny>>,
    seq1_aff_py: Vec<Py<PyAny>>,
    seq2_aff_py: Vec<Py<PyAny>>,
    seq1_aff_id: Vec<u32>,
    seq2_aff_id: Vec<u32>,
    seq1_tok_id: Vec<u32>,
    seq2_tok_id: Vec<u32>,
    seq1_is_open: Vec<bool>,
    seq2_is_open: Vec<bool>,
    open_to_close_id: HashMap<u32, u32>,
    node_affinity: Option<Py<PyAny>>,

    pool1: StatePool,
    pool2: StatePool,
    decomp1: HashMap<u32, Decomp>,
    decomp2: HashMap<u32, Decomp>,

    memo_emb: HashMap<u64, Arc<MatchResult>>,
    memo_iso: HashMap<u64, IsoResult>,
    affinity_cache: HashMap<u64, f64>,
    empty_match: Arc<MatchResult>,
}

impl<'py> Solver<'py> {
    fn new(
        py: Python<'py>,
        seq1_obj: Bound<'py, PyAny>,
        seq2_obj: Bound<'py, PyAny>,
        open_to_close_obj: Bound<'py, PyAny>,
        open_to_node_obj: Option<Bound<'py, PyAny>>,
        node_affinity: Option<Py<PyAny>>,
    ) -> PyResult<Self> {
        let open_to_close = open_to_close_obj.downcast_into::<PyDict>()?;
        let open_to_node = match open_to_node_obj {
            Some(mapping) if !mapping.is_none() => Some(mapping.unbind()),
            _ => None,
        };

        let seq1_py = seq1_obj
            .iter()?
            .map(|item| item.map(|x| x.unbind()))
            .collect::<PyResult<Vec<_>>>()?;
        let seq2_py = seq2_obj
            .iter()?
            .map(|item| item.map(|x| x.unbind()))
            .collect::<PyResult<Vec<_>>>()?;

        let mut interner = Interner::new(py);
        let mut open_to_close_id = HashMap::default();
        for (k, v) in open_to_close.iter() {
            let ok = interner.id_for(&k)?;
            let cv = interner.id_for(&v)?;
            open_to_close_id.insert(ok, cv);
        }

        let (seq1_tok_id, seq1_aff_id, seq1_aff_py) = Self::encode_sequence(
            py,
            &mut interner,
            &seq1_py,
            open_to_node.as_ref(),
        )?;
        let (seq2_tok_id, seq2_aff_id, seq2_aff_py) = Self::encode_sequence(
            py,
            &mut interner,
            &seq2_py,
            open_to_node.as_ref(),
        )?;

        let seq1_is_open = seq1_tok_id
            .iter()
            .map(|tid| open_to_close_id.contains_key(tid))
            .collect::<Vec<_>>();
        let seq2_is_open = seq2_tok_id
            .iter()
            .map(|tid| open_to_close_id.contains_key(tid))
            .collect::<Vec<_>>();

        let len1 = seq1_py.len();
        let len2 = seq2_py.len();
        let state_cap1 = len1.saturating_mul(8).max(64);
        let state_cap2 = len2.saturating_mul(8).max(64);
        let memo_cap = ((len1.saturating_mul(len2)) / 2).clamp(1024, 2_000_000);

        let mut pool1 = StatePool::with_capacity(state_cap1);
        let mut pool2 = StatePool::with_capacity(state_cap2);
        pool1.intern_key(StateKey::full(len1));
        pool2.intern_key(StateKey::full(len2));
        pool1.intern_key(StateKey::empty());
        pool2.intern_key(StateKey::empty());

        Ok(Self {
            py,
            seq1_obj,
            seq2_obj,
            seq1_py,
            seq2_py,
            seq1_aff_py,
            seq2_aff_py,
            seq1_aff_id,
            seq2_aff_id,
            seq1_tok_id,
            seq2_tok_id,
            seq1_is_open,
            seq2_is_open,
            open_to_close_id,
            node_affinity,
            pool1,
            pool2,
            decomp1: HashMap::with_capacity_and_hasher(state_cap1, Default::default()),
            decomp2: HashMap::with_capacity_and_hasher(state_cap2, Default::default()),
            memo_emb: HashMap::with_capacity_and_hasher(memo_cap, Default::default()),
            memo_iso: HashMap::with_capacity_and_hasher(memo_cap, Default::default()),
            affinity_cache: HashMap::with_capacity_and_hasher(memo_cap, Default::default()),
            empty_match: Arc::new(MatchResult::default()),
        })
    }

    fn encode_sequence(
        py: Python<'py>,
        interner: &mut Interner<'py>,
        seq: &[Py<PyAny>],
        open_to_node: Option<&Py<PyAny>>,
    ) -> PyResult<(Vec<u32>, Vec<u32>, Vec<Py<PyAny>>)> {
        let mut tok_ids = Vec::with_capacity(seq.len());
        let mut aff_ids = Vec::with_capacity(seq.len());
        let mut aff_py = Vec::with_capacity(seq.len());
        for tok in seq {
            let tokb = tok.bind(py);
            tok_ids.push(interner.id_for(&tokb)?);
            let mapped = if let Some(map) = open_to_node {
                match map.bind(py).get_item(tokb) {
                    Ok(v) => v,
                    Err(_) => tokb.clone(),
                }
            } else {
                tokb.clone()
            };
            aff_ids.push(interner.id_for(&mapped)?);
            aff_py.push(mapped.unbind());
        }
        Ok((tok_ids, aff_ids, aff_py))
    }

    #[inline]
    fn memo_key(a: u32, b: u32) -> u64 {
        ((a as u64) << 32) | (b as u64)
    }

    fn affinity(&mut self, tok1: u32, tok2: u32) -> PyResult<f64> {
        let key = Self::memo_key(tok1, tok2);
        if let Some(v) = self.affinity_cache.get(&key) {
            return Ok(*v);
        }

        let i1 = tok1 as usize;
        let i2 = tok2 as usize;
        let val = if let Some(ref func) = self.node_affinity {
            let n1 = self.seq1_aff_py[i1].bind(self.py);
            let n2 = self.seq2_aff_py[i2].bind(self.py);
            let out = func.bind(self.py).call1((n1, n2))?;
            if out.is_truthy()? {
                out.extract::<f64>()?
            } else {
                0.0
            }
        } else {
            if self.seq1_aff_id[i1] == self.seq2_aff_id[i2] {
                1.0
            } else {
                0.0
            }
        };
        self.affinity_cache.insert(key, val);
        Ok(val)
    }

    fn decompose1(&mut self, sid: u32) -> PyResult<Decomp> {
        if let Some(d) = self.decomp1.get(&sid) {
            return Ok(d.clone());
        }
        let state = self.pool1.get(sid);
        if state.len == 0 {
            return Err(pyo3::exceptions::PyValueError::new_err("Cannot decompose empty state"));
        }

        let mut depth = 0i32;
        let mut match_pos = None;
        let mut pos = 0u32;
        for r in &state.ranges {
            for idx in r.start..r.end {
                let i = idx as usize;
                if self.seq1_is_open[i] {
                    depth += 1;
                } else {
                    depth -= 1;
                    if depth == 0 {
                        match_pos = Some(pos);
                        break;
                    }
                }
                pos += 1;
            }
            if match_pos.is_some() {
                break;
            }
        }
        let m = match_pos.ok_or_else(|| pyo3::exceptions::PyValueError::new_err("No matching close token found"))?;

        let a = self.pool1.first(sid).unwrap_or(0);
        let b = self.pool1.index_at_pos(sid, m).unwrap_or(0);
        let open_id = self.seq1_tok_id[a as usize];
        let close_id = self.seq1_tok_id[b as usize];
        if self.open_to_close_id.get(&open_id) != Some(&close_id) {
            return Err(pyo3::exceptions::PyValueError::new_err("Mismatched close token"));
        }

        let head = self.pool1.slice_by_pos(sid, 1, m);
        let tail = self.pool1.slice_by_pos(sid, m + 1, state.len);
        let head_tail = self.pool1.concat(&head, &tail);

        let d = Decomp {
            a,
            b,
            head: self.pool1.intern_key(head),
            tail: self.pool1.intern_key(tail),
            head_tail: self.pool1.intern_key(head_tail),
        };
        self.decomp1.insert(sid, d.clone());
        Ok(d)
    }

    fn decompose2(&mut self, sid: u32) -> PyResult<Decomp> {
        if let Some(d) = self.decomp2.get(&sid) {
            return Ok(d.clone());
        }
        let state = self.pool2.get(sid);
        if state.len == 0 {
            return Err(pyo3::exceptions::PyValueError::new_err("Cannot decompose empty state"));
        }

        let mut depth = 0i32;
        let mut match_pos = None;
        let mut pos = 0u32;
        for r in &state.ranges {
            for idx in r.start..r.end {
                let i = idx as usize;
                if self.seq2_is_open[i] {
                    depth += 1;
                } else {
                    depth -= 1;
                    if depth == 0 {
                        match_pos = Some(pos);
                        break;
                    }
                }
                pos += 1;
            }
            if match_pos.is_some() {
                break;
            }
        }
        let m = match_pos.ok_or_else(|| pyo3::exceptions::PyValueError::new_err("No matching close token found"))?;

        let a = self.pool2.first(sid).unwrap_or(0);
        let b = self.pool2.index_at_pos(sid, m).unwrap_or(0);
        let open_id = self.seq2_tok_id[a as usize];
        let close_id = self.seq2_tok_id[b as usize];
        if self.open_to_close_id.get(&open_id) != Some(&close_id) {
            return Err(pyo3::exceptions::PyValueError::new_err("Mismatched close token"));
        }

        let head = self.pool2.slice_by_pos(sid, 1, m);
        let tail = self.pool2.slice_by_pos(sid, m + 1, state.len);
        let head_tail = self.pool2.concat(&head, &tail);

        let d = Decomp {
            a,
            b,
            head: self.pool2.intern_key(head),
            tail: self.pool2.intern_key(tail),
            head_tail: self.pool2.intern_key(head_tail),
        };
        self.decomp2.insert(sid, d.clone());
        Ok(d)
    }

    #[inline]
    fn better_match(&self, cand: &MatchResult, best: &MatchResult) -> bool {
        if cand.val > best.val {
            return true;
        }
        if cand.val < best.val {
            return false;
        }
        if cand.s1 > best.s1 {
            return true;
        }
        if cand.s1 < best.s1 {
            return false;
        }
        cand.s2 > best.s2
    }

    fn emb(&mut self, s1: u32, s2: u32) -> PyResult<Arc<MatchResult>> {
        if self.pool1.is_empty(s1) || self.pool2.is_empty(s2) {
            return Ok(self.empty_match.clone());
        }
        let key = Self::memo_key(s1, s2);
        if let Some(found) = self.memo_emb.get(&key) {
            return Ok(found.clone());
        }

        let d1 = self.decompose1(s1)?;
        let d2 = self.decompose2(s2)?;

        let mut best = self.emb(d1.head_tail, s2)?;
        let cand2 = self.emb(s1, d2.head_tail)?;
        if self.better_match(&cand2, &best) {
            best = cand2;
        }

        let aff = self.affinity(d1.a, d2.a)?;
        if aff > 0.0 {
            let h = self.emb(d1.head, d2.head)?;
            let t = self.emb(d1.tail, d2.tail)?;
            let mut s1v = Vec::with_capacity(h.s1.len() + t.s1.len() + 2);
            s1v.push(d1.a);
            s1v.extend_from_slice(&h.s1);
            s1v.push(d1.b);
            s1v.extend_from_slice(&t.s1);

            let mut s2v = Vec::with_capacity(h.s2.len() + t.s2.len() + 2);
            s2v.push(d2.a);
            s2v.extend_from_slice(&h.s2);
            s2v.push(d2.b);
            s2v.extend_from_slice(&t.s2);

            let cand = Arc::new(MatchResult {
                val: h.val + t.val + aff,
                s1: s1v,
                s2: s2v,
            });
            if self.better_match(&cand, &best) {
                best = cand;
            }
        }

        self.memo_emb.insert(key, best.clone());
        Ok(best)
    }

    fn iso(&mut self, s1: u32, s2: u32) -> PyResult<IsoResult> {
        if self.pool1.is_empty(s1) || self.pool2.is_empty(s2) {
            return Ok(IsoResult::default());
        }
        let key = Self::memo_key(s1, s2);
        if let Some(found) = self.memo_iso.get(&key) {
            return Ok(found.clone());
        }

        let d1 = self.decompose1(s1)?;
        let d2 = self.decompose2(s2)?;

        let r_h1s2 = self.iso(d1.head, s2)?;
        let r_t1s2 = self.iso(d1.tail, s2)?;
        let r_s1h2 = self.iso(s1, d2.head)?;
        let r_s1t2 = self.iso(s1, d2.tail)?;

        let mut any = MatchResult::default();
        for cand in [
            r_h1s2.any.clone(),
            r_t1s2.any.clone(),
            r_s1h2.any.clone(),
            r_s1t2.any.clone(),
        ] {
            if cand.val > any.val {
                any = cand;
            }
        }

        let mut lvl = MatchResult::default();
        for cand in [r_s1t2.lvl.clone(), r_t1s2.lvl.clone()] {
            if cand.val > lvl.val {
                lvl = cand;
            }
        }

        let aff = self.affinity(d1.a, d2.a)?;
        if aff > 0.0 {
            let r_h1h2 = self.iso(d1.head, d2.head)?;
            let r_t1t2 = self.iso(d1.tail, d2.tail)?;
            let mut s1v = Vec::with_capacity(r_h1h2.lvl.s1.len() + r_t1t2.lvl.s1.len() + 2);
            s1v.push(d1.a);
            s1v.extend_from_slice(&r_h1h2.lvl.s1);
            s1v.push(d1.b);
            s1v.extend_from_slice(&r_t1t2.lvl.s1);
            let mut s2v = Vec::with_capacity(r_h1h2.lvl.s2.len() + r_t1t2.lvl.s2.len() + 2);
            s2v.push(d2.a);
            s2v.extend_from_slice(&r_h1h2.lvl.s2);
            s2v.push(d2.b);
            s2v.extend_from_slice(&r_t1t2.lvl.s2);
            let cand = MatchResult {
                val: r_h1h2.lvl.val + r_t1t2.lvl.val + aff,
                s1: s1v,
                s2: s2v,
            };
            if cand.val > lvl.val {
                lvl = cand;
            }
        }

        if lvl.val >= any.val {
            any = lvl.clone();
        }

        let out = IsoResult { any, lvl };
        self.memo_iso.insert(key, out.clone());
        Ok(out)
    }

    fn indices_to_seq(&self, which: u8, idxs: &[u32]) -> PyResult<PyObject> {
        let (template, seq) = if which == 1 {
            (&self.seq1_obj, &self.seq1_py)
        } else {
            (&self.seq2_obj, &self.seq2_py)
        };

        if template.is_instance_of::<PyString>() {
            let mut out = String::new();
            for &i in idxs {
                out.push_str(&seq[i as usize].bind(self.py).extract::<String>()?);
            }
            Ok(PyString::new_bound(self.py, &out).into_any().unbind())
        } else if template.is_instance_of::<PyTuple>() {
            let items = idxs.iter().map(|&i| seq[i as usize].bind(self.py));
            Ok(PyTuple::new_bound(self.py, items).into_any().unbind())
        } else if template.is_instance_of::<PyList>() {
            let items = idxs.iter().map(|&i| seq[i as usize].bind(self.py));
            Ok(PyList::new_bound(self.py, items).into_any().unbind())
        } else {
            let items = idxs.iter().map(|&i| seq[i as usize].bind(self.py));
            Ok(PyTuple::new_bound(self.py, items).into_any().unbind())
        }
    }
}

#[pyfunction(signature = (seq1, seq2, open_to_close, open_to_node=None, node_affinity=None))]
fn longest_common_balanced_embedding(
    py: Python<'_>,
    seq1: PyObject,
    seq2: PyObject,
    open_to_close: PyObject,
    open_to_node: Option<PyObject>,
    node_affinity: Option<PyObject>,
) -> PyResult<PyObject> {
    let mut solver = Solver::new(
        py,
        seq1.bind(py).clone(),
        seq2.bind(py).clone(),
        open_to_close.bind(py).clone(),
        open_to_node.map(|x| x.bind(py).clone()),
        node_affinity,
    )?;

    let s1 = 0u32;
    let s2 = 0u32;
    let out = solver.emb(s1, s2)?;
    let best1 = solver.indices_to_seq(1, &out.s1)?;
    let best2 = solver.indices_to_seq(2, &out.s2)?;
    Ok((best1, best2, out.val).into_py(py))
}

#[pyfunction(signature = (seq1, seq2, open_to_close, open_to_node=None, node_affinity=None))]
fn longest_common_balanced_isomorphism(
    py: Python<'_>,
    seq1: PyObject,
    seq2: PyObject,
    open_to_close: PyObject,
    open_to_node: Option<PyObject>,
    node_affinity: Option<PyObject>,
) -> PyResult<PyObject> {
    let mut solver = Solver::new(
        py,
        seq1.bind(py).clone(),
        seq2.bind(py).clone(),
        open_to_close.bind(py).clone(),
        open_to_node.map(|x| x.bind(py).clone()),
        node_affinity,
    )?;

    let s1 = 0u32;
    let s2 = 0u32;
    let out = solver.iso(s1, s2)?.any;
    let best1 = solver.indices_to_seq(1, &out.s1)?;
    let best2 = solver.indices_to_seq(2, &out.s2)?;
    Ok((best1, best2, out.val).into_py(py))
}

#[pymodule]
fn _rust(_py: Python<'_>, module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(longest_common_balanced_embedding, module)?)?;
    module.add_function(wrap_pyfunction!(longest_common_balanced_isomorphism, module)?)?;
    Ok(())
}
