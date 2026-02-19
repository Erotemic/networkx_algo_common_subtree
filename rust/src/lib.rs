use pyo3::prelude::*;
use pyo3::types::PyDict;

#[pyfunction(signature = (seq1, seq2, open_to_close, open_to_node=None, node_affinity=None))]
fn longest_common_balanced_embedding(
    py: Python<'_>,
    seq1: PyObject,
    seq2: PyObject,
    open_to_close: PyObject,
    open_to_node: Option<PyObject>,
    node_affinity: Option<PyObject>,
) -> PyResult<PyObject> {
    let module = py.import_bound("networkx_algo_common_subtree.balanced_embedding")?;
    let kwargs = PyDict::new_bound(py);
    kwargs.set_item("open_to_node", open_to_node.unwrap_or_else(|| py.None().into_py(py)))?;
    kwargs.set_item("node_affinity", node_affinity.unwrap_or_else(|| "auto".into_py(py)))?;
    kwargs.set_item("impl", "iter")?;
    let result = module
        .getattr("longest_common_balanced_embedding")?
        .call((seq1, seq2, open_to_close), Some(&kwargs))?;
    Ok(result.into_py(py))
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
    let module = py.import_bound("networkx_algo_common_subtree.balanced_isomorphism")?;
    let kwargs = PyDict::new_bound(py);
    kwargs.set_item("open_to_node", open_to_node.unwrap_or_else(|| py.None().into_py(py)))?;
    kwargs.set_item("node_affinity", node_affinity.unwrap_or_else(|| "auto".into_py(py)))?;
    kwargs.set_item("impl", "iter")?;
    let result = module
        .getattr("longest_common_balanced_isomorphism")?
        .call((seq1, seq2, open_to_close), Some(&kwargs))?;
    Ok(result.into_py(py))
}

#[pymodule]
fn _rust(_py: Python<'_>, module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(longest_common_balanced_embedding, module)?)?;
    module.add_function(wrap_pyfunction!(longest_common_balanced_isomorphism, module)?)?;
    Ok(())
}
