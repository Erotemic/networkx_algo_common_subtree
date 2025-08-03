#include <Python.h>
#include <stdlib.h>
#include <string.h>

/*
Pure C implementation of the longest common balanced subsequence embedding
algorithm. The algorithm operates entirely on C structures and only converts
between Python objects at the boundary.

For simplicity we only handle sequences that are UTF8 strings consisting of
single byte tokens. The node affinity function is restricted to either strict
character equality or always-true matching.
*/

typedef struct { const char *data; int len; } SeqView;

typedef struct {
    char map[256];
    unsigned char is_open[256];
} TokenMap;

typedef struct {
    SeqView seq;  // key
    char a;       // opening token
    char b;       // closing token
    SeqView head;
    SeqView tail;
    SeqView head_tail;
} Decomp;

typedef struct {
    Decomp *items;
    int count;
    int cap;
} DecompTable;

static void dtable_init(DecompTable *t){ t->items=NULL; t->count=0; t->cap=0; }
static void dtable_free(DecompTable *t){
    for(int i=0;i<t->count;i++){ free((void*)t->items[i].head_tail.data); }
    free(t->items);
}

static Decomp *dtable_lookup(DecompTable *t, SeqView seq){
    for(int i=0;i<t->count;i++){
        if(t->items[i].seq.data==seq.data && t->items[i].seq.len==seq.len)
            return &t->items[i];
    }
    return NULL;
}

static Decomp *dtable_add(DecompTable *t, Decomp item){
    if(t->count==t->cap){
        t->cap = t->cap? t->cap*2:16;
        t->items = realloc(t->items, t->cap * sizeof(Decomp));
    }
    t->items[t->count] = item;
    return &t->items[t->count++];
}

static Decomp *decompose(DecompTable *tbl, SeqView seq, const TokenMap *map){
    Decomp *found = dtable_lookup(tbl, seq);
    if(found) return found;
    const char *s = seq.data;
    int n = seq.len;
    char a = s[0];
    char want = map->map[(unsigned char)a];
    int stack=1; int close_idx=-1;
    for(int i=1;i<n;i++){
        char tok = s[i];
        if(map->is_open[(unsigned char)tok]) stack++;
        else stack--;
        if(stack==0 && tok==want){ close_idx=i; break; }
    }
    if(close_idx<0) return NULL; // invalid sequence
    Decomp item;
    item.seq = seq;
    item.a = a;
    item.b = want;
    item.head.data = s+1;
    item.head.len = close_idx-1;
    item.tail.data = s+close_idx+1;
    item.tail.len = n - close_idx -1;
    int ht_len = item.head.len + item.tail.len;
    char *ht = malloc(ht_len ? ht_len : 1);
    memcpy(ht, item.head.data, item.head.len);
    memcpy(ht+item.head.len, item.tail.data, item.tail.len);
    item.head_tail.data = ht;
    item.head_tail.len = ht_len;
    return dtable_add(tbl, item);
}

typedef struct {
    SeqView s1, s2;
    double val;
    SeqView out1, out2;
} MemoEntry;

typedef struct {
    MemoEntry *items;
    int count;
    int cap;
} MemoTable;

static void memo_init(MemoTable *m){ m->items=NULL; m->count=0; m->cap=0; }
static void memo_free(MemoTable *m){ free(m->items); }

static MemoEntry *memo_lookup(MemoTable *m, SeqView s1, SeqView s2){
    for(int i=0;i<m->count;i++){
        MemoEntry *e=&m->items[i];
        if(e->s1.data==s1.data && e->s1.len==s1.len &&
           e->s2.data==s2.data && e->s2.len==s2.len){
            return e;
        }
    }
    return NULL;
}

static MemoEntry *memo_add(MemoTable *m, MemoEntry item){
    if(m->count==m->cap){
        m->cap = m->cap? m->cap*2:16;
        m->items = realloc(m->items, m->cap*sizeof(MemoEntry));
    }
    m->items[m->count] = item;
    return &m->items[m->count++];
}

static SeqView concat(const SeqView *arr, int n){
    int len=0;
    for(int i=0;i<n;i++) len += arr[i].len;
    char *buf = malloc(len? len:1);
    char *p=buf;
    for(int i=0;i<n;i++){ memcpy(p, arr[i].data, arr[i].len); p += arr[i].len; }
    SeqView out={buf,len};
    return out;
}

typedef double (*AffFn)(char, char);
static double aff_eq(char a, char b){ return a==b ? 1.0 : 0.0; }
static double aff_any(char a, char b){ (void)a; (void)b; return 1.0; }

static void lcse_rec(SeqView s1, SeqView s2, const TokenMap *map, AffFn aff,
                     DecompTable *dt, MemoTable *memo,
                     double *out_val, SeqView *out1, SeqView *out2){
    if(s1.len==0 || s2.len==0){
        *out_val = 0.0;
        out1->data = ""; out1->len = 0;
        out2->data = ""; out2->len = 0;
        return;
    }
    MemoEntry *me = memo_lookup(memo, s1, s2);
    if(me){
        *out_val = me->val; *out1 = me->out1; *out2 = me->out2; return; }

    Decomp *d1 = decompose(dt, s1, map);
    Decomp *d2 = decompose(dt, s2, map);
    double val; SeqView best1, best2;
    lcse_rec(d1->head_tail, s2, map, aff, dt, memo, &val, &best1, &best2);
    double best_val = val; SeqView out_best1 = best1; SeqView out_best2 = best2;

    double val2; SeqView cand1, cand2;
    lcse_rec(s1, d2->head_tail, map, aff, dt, memo, &val2, &cand1, &cand2);
    if(val2 > best_val){ best_val=val2; out_best1=cand1; out_best2=cand2; }

    double affinity = aff(d1->a, d2->a);
    if(affinity > 0){
        double vh; SeqView h1,h2; lcse_rec(d1->head, d2->head, map, aff, dt, memo, &vh, &h1, &h2);
        double vt; SeqView t1,t2; lcse_rec(d1->tail, d2->tail, map, aff, dt, memo, &vt, &t1, &t2);
        SeqView parts1[4] = {{&d1->a,1}, h1, {&d1->b,1}, t1};
        SeqView parts2[4] = {{&d2->a,1}, h2, {&d2->b,1}, t2};
        SeqView seq1 = concat(parts1,4);
        SeqView seq2 = concat(parts2,4);
        double v3 = vh + vt + affinity;
        if(v3 > best_val){ best_val=v3; out_best1=seq1; out_best2=seq2; }
        else { free((void*)seq1.data); free((void*)seq2.data); }
    }

    MemoEntry new = {s1,s2,best_val,out_best1,out_best2};
    memo_add(memo,new);
    *out_val = best_val; *out1 = out_best1; *out2 = out_best2;
}

static int parse_map(PyObject *dict, TokenMap *map){
    memset(map,0,sizeof(*map));
    PyObject *key, *val; Py_ssize_t pos=0;
    while(PyDict_Next(dict,&pos,&key,&val)){
        if(!PyUnicode_Check(key) || !PyUnicode_Check(val)) return -1;
        if(PyUnicode_GET_LENGTH(key)!=1 || PyUnicode_GET_LENGTH(val)!=1) return -1;
        char k = PyUnicode_READ_CHAR(key,0);
        char v = PyUnicode_READ_CHAR(val,0);
        map->map[(unsigned char)k] = v;
        map->is_open[(unsigned char)k] = 1;
    }
    return 0;
}

static PyObject *lcse_wrapper(PyObject *self, PyObject *args){
    const char *s1; const char *s2; Py_ssize_t n1,n2; PyObject *map_dict; PyObject *aff_obj=Py_None;
    if(!PyArg_ParseTuple(args,"s#s#O|O",&s1,&n1,&s2,&n2,&map_dict,&aff_obj)) return NULL;
    TokenMap map; if(parse_map(map_dict,&map)<0){ PyErr_SetString(PyExc_ValueError,"invalid map"); return NULL; }
    AffFn aff = aff_eq; if(aff_obj==Py_None) aff = aff_any;
    SeqView seq1={s1,(int)n1}, seq2={s2,(int)n2};
    DecompTable dt; dtable_init(&dt); MemoTable memo; memo_init(&memo);
    double val; SeqView out1,out2;
    lcse_rec(seq1,seq2,&map,aff,&dt,&memo,&val,&out1,&out2);
    PyObject *py_out1 = PyUnicode_FromStringAndSize(out1.data,out1.len);
    PyObject *py_out2 = PyUnicode_FromStringAndSize(out2.data,out2.len);
    PyObject *py_pair = PyTuple_Pack(2, py_out1, py_out2);
    PyObject *py_val = PyFloat_FromDouble(val);
    PyObject *result = PyTuple_Pack(2, py_val, py_pair);
    Py_DECREF(py_out1); Py_DECREF(py_out2); Py_DECREF(py_pair); Py_DECREF(py_val);
    dtable_free(&dt); memo_free(&memo);
    free((void*)out1.data); free((void*)out2.data);
    return result;
}

static PyMethodDef methods[] = {
    {"_lcse_recurse_c", lcse_wrapper, METH_VARARGS, "pure C lcse"},
    {NULL, NULL, 0, NULL}
};

static struct PyModuleDef moduledef = {PyModuleDef_HEAD_INIT, "balanced_embedding_c", NULL, -1, methods};
PyMODINIT_FUNC PyInit_balanced_embedding_c(void){ return PyModule_Create(&moduledef); }

