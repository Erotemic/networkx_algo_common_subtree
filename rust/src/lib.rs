use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyList, PyString, PyTuple};
use std::cmp::Ordering;
use rustc_hash::FxHashMap as HashMap;

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

#[derive(Clone)]
struct Decomp {
    a: u32,
    b: u32,
    head: Vec<u32>,
    tail: Vec<u32>,
    head_tail: Vec<u32>,
}

type State = Vec<u32>;
type StateKey = (State, State);

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
    close_to_open_id: HashMap<u32, u32>,
    node_affinity: Option<Py<PyAny>>,
    decomp1: HashMap<State, Decomp>,
    decomp2: HashMap<State, Decomp>,
    memo_emb: HashMap<StateKey, MatchResult>,
    memo_iso: HashMap<StateKey, IsoResult>,
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
        let mut close_to_open_id = HashMap::default();
        for (k, v) in open_to_close.iter() {
            let ok = interner.id_for(&k)?;
            let cv = interner.id_for(&v)?;
            open_to_close_id.insert(ok, cv);
            close_to_open_id.insert(cv, ok);
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
            close_to_open_id,
            node_affinity,
            decomp1: HashMap::default(),
            decomp2: HashMap::default(),
            memo_emb: HashMap::default(),
            memo_iso: HashMap::default(),
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
            let tid = interner.id_for(&tokb)?;
            tok_ids.push(tid);
            let mapped = if let Some(map) = open_to_node {
                match map.bind(py).get_item(tokb) {
                    Ok(v) => v,
                    Err(_) => tokb.clone(),
                }
            } else {
                tokb.clone()
            };
            let aid = interner.id_for(&mapped)?;
            aff_ids.push(aid);
            aff_py.push(mapped.unbind());
        }
        Ok((tok_ids, aff_ids, aff_py))
    }

    fn affinity(&self, tok1: u32, tok2: u32, which1: u8, which2: u8) -> PyResult<f64> {
        let i1 = tok1 as usize;
        let i2 = tok2 as usize;
        if let Some(ref func) = self.node_affinity {
            let n1 = if which1 == 1 {
                self.seq1_aff_py[i1].bind(self.py)
            } else {
                self.seq2_aff_py[i1].bind(self.py)
            };
            let n2 = if which2 == 1 {
                self.seq1_aff_py[i2].bind(self.py)
            } else {
                self.seq2_aff_py[i2].bind(self.py)
            };
            let out = func.bind(self.py).call1((n1, n2))?;
            if out.is_truthy()? {
                out.extract::<f64>()
            } else {
                Ok(0.0)
            }
        } else {
            let a1 = if which1 == 1 {
                self.seq1_aff_id[i1]
            } else {
                self.seq2_aff_id[i1]
            };
            let a2 = if which2 == 1 {
                self.seq1_aff_id[i2]
            } else {
                self.seq2_aff_id[i2]
            };
            if a1 == a2 {
                Ok(1.0)
            } else {
                Ok(0.0)
            }
        }
    }

    fn decompose(&mut self, which: u8, state: &[u32]) -> PyResult<Decomp> {
        if state.is_empty() {
            return Err(pyo3::exceptions::PyValueError::new_err("Cannot decompose empty state"));
        }
        let cache = if which == 1 {
            &mut self.decomp1
        } else {
            &mut self.decomp2
        };
        if let Some(d) = cache.get(state) {
            return Ok(d.clone());
        }

        let (seq_tok_id, seq_is_open) = if which == 1 {
            (&self.seq1_tok_id, &self.seq1_is_open)
        } else {
            (&self.seq2_tok_id, &self.seq2_is_open)
        };

        let mut depth = 0i32;
        let mut match_pos = None;
        for (pos, &idx) in state.iter().enumerate() {
            let i = idx as usize;
            if seq_is_open[i] {
                depth += 1;
            } else {
                if depth == 0 {
                    return Err(pyo3::exceptions::PyValueError::new_err("Invalid balanced sequence"));
                }
                depth -= 1;
                if depth == 0 {
                    match_pos = Some(pos);
                    break;
                }
            }

            // quick structural validation for close tokens
            if !seq_is_open[i] {
                let close_id = seq_tok_id[i];
                if !self.close_to_open_id.contains_key(&close_id) {
                    return Err(pyo3::exceptions::PyKeyError::new_err(
                        "Token missing from open_to_close mapping",
                    ));
                }
            }
        }

        let m = match_pos.ok_or_else(|| {
            pyo3::exceptions::PyValueError::new_err("No matching close token found")
        })?;
        let a = state[0];
        let b = state[m];

        // validate matching type for first open and detected close
        let a_tok = seq_tok_id[a as usize];
        let b_tok = seq_tok_id[b as usize];
        if self.open_to_close_id.get(&a_tok) != Some(&b_tok) {
            return Err(pyo3::exceptions::PyValueError::new_err("Mismatched close token"));
        }

        let head = state[1..m].to_vec();
        let tail = state[(m + 1)..].to_vec();
        let mut head_tail = Vec::with_capacity(head.len() + tail.len());
        head_tail.extend_from_slice(&head);
        head_tail.extend_from_slice(&tail);

        let d = Decomp {
            a,
            b,
            head,
            tail,
            head_tail,
        };
        cache.insert(state.to_vec(), d.clone());
        Ok(d)
    }

    fn better_match(&self, cand: &MatchResult, best: &MatchResult) -> bool {
        if cand.val > best.val {
            return true;
        }
        if cand.val < best.val {
            return false;
        }
        match cand.s1.cmp(&best.s1) {
            Ordering::Greater => return true,
            Ordering::Less => return false,
            Ordering::Equal => {}
        }
        cand.s2 > best.s2
    }

    fn emb(&mut self, s1: State, s2: State) -> PyResult<MatchResult> {
        if s1.is_empty() || s2.is_empty() {
            return Ok(MatchResult::default());
        }
        let key = (s1.clone(), s2.clone());
        if let Some(found) = self.memo_emb.get(&key) {
            return Ok(found.clone());
        }

        let d1 = self.decompose(1, &s1)?;
        let d2 = self.decompose(2, &s2)?;

        let mut best = self.emb(d1.head_tail.clone(), s2.clone())?;
        let cand2 = self.emb(s1.clone(), d2.head_tail.clone())?;
        if self.better_match(&cand2, &best) {
            best = cand2;
        }

        let aff = self.affinity(d1.a, d2.a, 1, 2)?;
        if aff > 0.0 {
            let h = self.emb(d1.head.clone(), d2.head.clone())?;
            let t = self.emb(d1.tail.clone(), d2.tail.clone())?;
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

            let cand = MatchResult {
                val: h.val + t.val + aff,
                s1: s1v,
                s2: s2v,
            };
            if self.better_match(&cand, &best) {
                best = cand;
            }
        }

        self.memo_emb.insert(key, best.clone());
        Ok(best)
    }

    fn iso(&mut self, s1: State, s2: State) -> PyResult<IsoResult> {
        if s1.is_empty() || s2.is_empty() {
            return Ok(IsoResult::default());
        }
        let key = (s1.clone(), s2.clone());
        if let Some(found) = self.memo_iso.get(&key) {
            return Ok(found.clone());
        }

        let d1 = self.decompose(1, &s1)?;
        let d2 = self.decompose(2, &s2)?;

        let r_h1s2 = self.iso(d1.head.clone(), s2.clone())?;
        let r_t1s2 = self.iso(d1.tail.clone(), s2.clone())?;
        let r_s1h2 = self.iso(s1.clone(), d2.head.clone())?;
        let r_s1t2 = self.iso(s1.clone(), d2.tail.clone())?;

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

        let aff = self.affinity(d1.a, d2.a, 1, 2)?;
        if aff > 0.0 {
            let r_h1h2 = self.iso(d1.head.clone(), d2.head.clone())?;
            let r_t1t2 = self.iso(d1.tail.clone(), d2.tail.clone())?;
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

    let s1 = (0..solver.seq1_py.len() as u32).collect::<Vec<_>>();
    let s2 = (0..solver.seq2_py.len() as u32).collect::<Vec<_>>();
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

    let s1 = (0..solver.seq1_py.len() as u32).collect::<Vec<_>>();
    let s2 = (0..solver.seq2_py.len() as u32).collect::<Vec<_>>();
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
