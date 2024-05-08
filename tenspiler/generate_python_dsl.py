from tenspiler.constants import TENSPILER_FNS

for fn in set(TENSPILER_FNS):
    if fn.body() is None:
        continue
    python_fn = fn.to_python()
    print(python_fn)
    print()
