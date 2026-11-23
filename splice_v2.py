"""One-shot splice: v2 correctness/benchmark layer into engine.py."""
P = "src/engine/engine.py"
s = open(P).read()
v2 = open("/tmp/v2.py").read()


def rep(old, new):
    global s
    assert old in s, "MISSING: " + old[:100]
    s = s.replace(old, new, 1)


def replace_func(name, new_code):
    global s
    import re
    m = re.search(r"^def %s\(" % re.escape(name), s, re.M)
    assert m, name
    m2 = re.search(r"^(def |class |# -{10,}|# ---- )", s[m.end():], re.M)
    end = m.end() + m2.start() if m2 else len(s)
    s = s[:m.start()] + new_code.rstrip() + "\n\n\n" + s[end:]


# ---------------- imports + v2 layer -----------------------------------------
rep("import gc\n", "import gc\nimport types\n")
anchor = "# --------------------------------------------------------------------------\n# Optimizer transformations"
assert anchor in s
s = s.replace(anchor, v2 + "\n\n" + anchor, 1)

# ---------------- stdin for run_program --------------------------------------
rep("def run_program(code, repeats=5, budget=1.0):", 'def run_program(code, repeats=5, budget=1.0, stdin=""):')
rep('''        ns = {"__name__": "__main__"}
        buf = io.StringIO()
        old = sys.stdout
        sys.stdout = buf''', '''        ns = {"__name__": "__main__"}
        buf = io.StringIO()
        old = sys.stdout
        old_in = sys.stdin
        sys.stdout = buf
        sys.stdin = io.StringIO(stdin)''')
rep('''        finally:
            sys.stdout = old
        if i == 0:''', '''        finally:
            sys.stdout = old
            sys.stdin = old_in
        if i == 0:''')

# ---------------- guarded hash rewrites --------------------------------------
replace_func("apply_shadow_set", '''def apply_shadow_set(tree, payload):
    scope, s, name, sname, tests, appends = payload
    for t in tests:
        left = ast.unparse(t.left)
        fast = f"{left} in {sname}"
        slow = f"{left} in {name}"
        expr = ast.parse(f"(({fast}) if {sname} is not None else ({slow}))", mode="eval").body
        if isinstance(t.ops[0], ast.NotIn):
            expr = ast.UnaryOp(op=ast.Not(), operand=expr)
        _replace_node(tree, t, expr)
    for a in appends:
        expr_stmt = a._parent
        lst, idx = _parent_stmt_list(expr_stmt)
        if lst is None:
            continue
        add = ast.parse(f"if {sname} is not None:\\n    {sname}.add({ast.unparse(a.args[0])})").body[0]
        lst.insert(idx + 1, ast.fix_missing_locations(add))
    lst, idx = _parent_stmt_list(s)
    if lst is not None:
        guard = HASHSAFE.format(var=name)
        lst.insert(idx + 1, ast.parse(f"{sname} = set() if {guard} else None").body[0])
''')

replace_func("apply_membership", '''def apply_membership(tree, payload):
    scope, name, loop, lst, idx, set_name = payload
    for n in list(ast.walk(loop)):
        if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn)) and is_name(n.comparators[0], name):
            left = ast.unparse(n.left)
            expr = ast.parse(f"(({left} in {set_name}) if {set_name} is not None else ({left} in {name}))", mode="eval").body
            if isinstance(n.ops[0], ast.NotIn):
                expr = ast.UnaryOp(op=ast.Not(), operand=expr)
            _replace_node(tree, n, expr)
    guard = HASHSAFE.format(var=name)
    lst.insert(idx, ast.parse(f"{set_name} = set({name}) if {guard} else None").body[0])
''')

replace_func("apply_counter", '''def apply_counter(tree, payload):
    name, loop, lst, idx, cname = payload
    class R(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if call_name(node) == ".count" and is_name(node.func.value, name) and len(node.args) == 1 and isinstance(node.args[0], (ast.Name, ast.Subscript)):
                inner = ast.Subscript(value=ast.Name(id=cname, ctx=ast.Load()), slice=node.args[0], ctx=ast.Load())
                cond = ast.Compare(left=ast.Name(id=cname, ctx=ast.Load()), ops=[ast.IsNot()], comparators=[ast.Constant(value=None)])
                return ast.copy_location(ast.IfExp(test=cond, body=inner, orelse=node), node)
            return node
    R().visit(loop)
    guard = HASHSAFE.format(var=name)
    lst.insert(idx, ast.parse(f"{cname} = collections.Counter({name}) if {guard} else None").body[0])
    _ensure_import(tree, "collections")
''')

replace_func("apply_nested_eq", '''def apply_nested_eq(tree, payload):
    inner, outer, lst, idx, B, set_name, x, inner_stmts = payload
    yv = "_y_guard"
    fast = ast.Compare(left=ast.Name(id=x, ctx=ast.Load()), ops=[ast.In()], comparators=[ast.Name(id=set_name, ctx=ast.Load())])
    slow = ast.Call(func=ast.Name(id="any", ctx=ast.Load()), args=[ast.GeneratorExp(
        elt=ast.Compare(left=ast.Name(id=x, ctx=ast.Load()), ops=[ast.Eq()], comparators=[ast.Name(id=yv, ctx=ast.Load())]),
        generators=[ast.comprehension(target=ast.Name(id=yv, ctx=ast.Store()), iter=ast.Name(id=B, ctx=ast.Load()), ifs=[], is_async=0)])], keywords=[])
    test = ast.IfExp(test=ast.Compare(left=ast.Name(id=set_name, ctx=ast.Load()), ops=[ast.IsNot()], comparators=[ast.Constant(value=None)]),
                     body=fast, orelse=slow)
    new_if = ast.If(test=test, body=inner_stmts or [ast.Pass()], orelse=[])
    plist, pidx = _parent_stmt_list(inner)
    if plist is None:
        return
    plist[pidx] = ast.fix_missing_locations(new_if)
    guard = HASHSAFE.format(var=B)
    lst.insert(idx, ast.parse(f"{set_name} = set({B}) if {guard} else None").body[0])
''')

# pair rules: wrap the generated fast path in an ints-only guard with the ORIGINAL as fallback
rep('''                    changes.append(("replace_stmt", fn.name, (stmts, k, new_stmts), Change(
                        title, detail, fn.name, ast.unparse(s), _stmts_src(new_stmts))))''',
    '''                    fast = new_stmts
                    fallback = copy.deepcopy(stmts[k])
                    wrapped = [ast.fix_missing_locations(ast.If(
                        test=ast.parse(INTSAFE.format(var=A), mode="eval").body, body=fast, orelse=[fallback]))]
                    changes.append(("replace_stmt", fn.name, (stmts, k, wrapped), Change(
                        title + " (ints only, fallback kept)", detail, fn.name, ast.unparse(s), _stmts_src(wrapped))))''')
rep('''                    new_stmts = ast.parse(body).body
                    changes.append(("replace_stmt_import", fn.name, (stmts, k, new_stmts, ("collections", None)), Change(
                        title, detail, fn.name, ast.unparse(s), _stmts_src(new_stmts))))''',
    '''                    new_stmts = ast.parse(body).body
                    fallback = copy.deepcopy(stmts[k])
                    wrapped = [ast.fix_missing_locations(ast.If(
                        test=ast.parse(INTSAFE.format(var=A), mode="eval").body, body=new_stmts, orelse=[fallback]))]
                    changes.append(("replace_stmt_import", fn.name, (stmts, k, wrapped, ("collections", None)), Change(
                        title + " (ints only, fallback kept)", detail, fn.name, ast.unparse(s), _stmts_src(wrapped))))''')

# list_as_set is subsumed by the guarded shadow_set
rep('    "list_as_set": lambda t, a: t_list_as_set(t),\n', '')
rep('"membership", "list_as_set",', '"membership",')

open(P, "w").write(s)
print("v2 spliced; lists_as_set unregistered")
