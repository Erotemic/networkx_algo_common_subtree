use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyList, PyString, PyTuple};
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
struct MatchResult {
    val: f64,
    s1: Vec<usize>,
    s2: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
struct IsoResult {
    any: MatchResult,
    lvl: MatchResult,
}

#[derive(Clone)]
struct Decomp {
    a: usize,
    b: usize,
    head: Vec<usize>,
    tail: Vec<usize>,
    head_tail: Vec<usize>,
}

type StateKey = (Vec<usize>, Vec<usize>);

struct Solver<'py> {
    py: Python<'py>,
    seq1_obj: Bound<'py, PyAny>,
    seq2_obj: Bound<'py, PyAny>,
    seq1: Vec<Py<PyAny>>,
    seq2: Vec<Py<PyAny>>,
    open_to_close: Bound<'py, PyDict>,
    close_to_open: Bound<'py, PyDict>,
    open_to_node: Option<Py<PyAny>>,
    node_affinity: Option<Py<PyAny>>,
    decomp1: HashMap<Vec<usize>, Decomp>,
    decomp2: HashMap<Vec<usize>, Decomp>,
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
        let close_to_open = PyDict::new_bound(py);
        for (k, v) in open_to_close.iter() {
            close_to_open.set_item(v, k)?;
        }

        let open_to_node = match open_to_node_obj {
            Some(mapping) if !mapping.is_none() => Some(mapping.unbind()),
            _ => None,
        };

        let seq1 = seq1_obj
            .iter()?
            .map(|item| item.map(|x| x.unbind()))
            .collect::<PyResult<Vec<_>>>()?;
        let seq2 = seq2_obj
            .iter()?
            .map(|item| item.map(|x| x.unbind()))
            .collect::<PyResult<Vec<_>>>()?;

        Ok(Self {
            py,
            seq1_obj,
            seq2_obj,
            seq1,
            seq2,
            open_to_close,
            close_to_open,
            open_to_node,
            node_affinity,
            decomp1: HashMap::new(),
            decomp2: HashMap::new(),
            memo_emb: HashMap::new(),
            memo_iso: HashMap::new(),
        })
    }

    fn affinity(&self, tok1: usize, tok2: usize, which1: u8, which2: u8) -> PyResult<f64> {
        let t1 = if which1 == 1 {
            self.seq1[tok1].bind(self.py)
        } else {
            self.seq2[tok1].bind(self.py)
        };
        let t2 = if which2 == 1 {
            self.seq1[tok2].bind(self.py)
        } else {
            self.seq2[tok2].bind(self.py)
        };

        let n1 = if let Some(ref map) = self.open_to_node {
            match map.bind(self.py).get_item(t1) {
                Ok(v) => v,
                Err(_) => t1.clone(),
            }
        } else {
            t1.clone()
        };
        let n2 = if let Some(ref map) = self.open_to_node {
            match map.bind(self.py).get_item(t2) {
                Ok(v) => v,
                Err(_) => t2.clone(),
            }
        } else {
            t2.clone()
        };

        if let Some(ref func) = self.node_affinity {
            let out = func.bind(self.py).call1((n1, n2))?;
            if out.is_truthy()? {
                out.extract::<f64>()
            } else {
                Ok(0.0)
            }
        } else if n1.eq(n2)? {
            Ok(1.0)
        } else {
            Ok(0.0)
        }
    }

    fn decompose(&mut self, which: u8, state: &[usize]) -> PyResult<Decomp> {
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

        let seq = if which == 1 { &self.seq1 } else { &self.seq2 };
        let mut stack: Vec<usize> = Vec::new();
        let mut match_pos = None;
        for (pos, &idx) in state.iter().enumerate() {
            let tok = seq[idx].bind(self.py);
            if self.open_to_close.contains(tok)? {
                stack.push(idx);
            } else if self.close_to_open.contains(tok)? {
                let top = stack.pop().ok_or_else(|| {
                    pyo3::exceptions::PyValueError::new_err("Invalid balanced sequence")
                })?;
                let expected = self.close_to_open.get_item(tok)?.expect("close token in inverse");
                if !seq[top].bind(self.py).eq(expected)? {
                    return Err(pyo3::exceptions::PyValueError::new_err("Mismatched close token"));
                }
                if stack.is_empty() {
                    match_pos = Some(pos);
                    break;
                }
            } else {
                return Err(pyo3::exceptions::PyKeyError::new_err(
                    "Token missing from open_to_close mapping",
                ));
            }
        }

        let m = match_pos.ok_or_else(|| {
            pyo3::exceptions::PyValueError::new_err("No matching close token found")
        })?;
        let a = state[0];
        let b = state[m];
        let head = state[1..m].to_vec();
        let tail = state[(m + 1)..].to_vec();
        let mut head_tail = head.clone();
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


    fn better_match(&self, cand: &MatchResult, best: &MatchResult) -> PyResult<bool> {
        if cand.val > best.val {
            return Ok(true);
        }
        if cand.val < best.val {
            return Ok(false);
        }
        let cand1 = PyTuple::new_bound(self.py, cand.s1.iter().map(|&i| self.seq1[i].bind(self.py)));
        let best1 = PyTuple::new_bound(self.py, best.s1.iter().map(|&i| self.seq1[i].bind(self.py)));
        if cand1.gt(best1.clone())? {
            return Ok(true);
        }
        if cand1.lt(best1)? {
            return Ok(false);
        }
        let cand2 = PyTuple::new_bound(self.py, cand.s2.iter().map(|&i| self.seq2[i].bind(self.py)));
        let best2 = PyTuple::new_bound(self.py, best.s2.iter().map(|&i| self.seq2[i].bind(self.py)));
        cand2.gt(best2)
    }

    fn emb(&mut self, s1: Vec<usize>, s2: Vec<usize>) -> PyResult<MatchResult> {
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
        if self.better_match(&cand2, &best)? {
            best = cand2;
        }

        let aff = self.affinity(d1.a, d2.a, 1, 2)?;
        if aff > 0.0 {
            let h = self.emb(d1.head.clone(), d2.head.clone())?;
            let t = self.emb(d1.tail.clone(), d2.tail.clone())?;
            let mut s1v = vec![d1.a];
            s1v.extend_from_slice(&h.s1);
            s1v.push(d1.b);
            s1v.extend_from_slice(&t.s1);
            let mut s2v = vec![d2.a];
            s2v.extend_from_slice(&h.s2);
            s2v.push(d2.b);
            s2v.extend_from_slice(&t.s2);
            let cand = MatchResult {
                val: h.val + t.val + aff,
                s1: s1v,
                s2: s2v,
            };
            if self.better_match(&cand, &best)? {
                best = cand;
            }
        }

        self.memo_emb.insert(key, best.clone());
        Ok(best)
    }

    fn iso(&mut self, s1: Vec<usize>, s2: Vec<usize>) -> PyResult<IsoResult> {
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
            let mut s1v = vec![d1.a];
            s1v.extend_from_slice(&r_h1h2.lvl.s1);
            s1v.push(d1.b);
            s1v.extend_from_slice(&r_t1t2.lvl.s1);
            let mut s2v = vec![d2.a];
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

    fn indices_to_seq(&self, which: u8, idxs: &[usize]) -> PyResult<PyObject> {
        let (template, seq) = if which == 1 {
            (&self.seq1_obj, &self.seq1)
        } else {
            (&self.seq2_obj, &self.seq2)
        };

        if template.is_instance_of::<PyString>() {
            let mut out = String::new();
            for &i in idxs {
                out.push_str(&seq[i].bind(self.py).extract::<String>()?);
            }
            Ok(PyString::new_bound(self.py, &out).into_any().unbind())
        } else if template.is_instance_of::<PyTuple>() {
            let items = idxs.iter().map(|&i| seq[i].bind(self.py));
            Ok(PyTuple::new_bound(self.py, items).into_any().unbind())
        } else if template.is_instance_of::<PyList>() {
            let items = idxs.iter().map(|&i| seq[i].bind(self.py));
            Ok(PyList::new_bound(self.py, items).into_any().unbind())
        } else {
            let items = idxs.iter().map(|&i| seq[i].bind(self.py));
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

    let s1 = (0..solver.seq1.len()).collect::<Vec<_>>();
    let s2 = (0..solver.seq2.len()).collect::<Vec<_>>();
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

    let s1 = (0..solver.seq1.len()).collect::<Vec<_>>();
    let s2 = (0..solver.seq2.len()).collect::<Vec<_>>();
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
