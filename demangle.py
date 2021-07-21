import subprocess 
def demangle(names):
    args = ['c++filt', '-n']
    args.extend(names)
    pipe = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    stdout, _ = pipe.communicate()
    demangled = stdout.decode().split("\n")

    # Each line ends with a newline, so the final entry of the split output
    # will always be ''.
    assert(len(demangled) == len(names)+1)
    return demangled[:-1]

print(demangle(['_ZNSt15basic_stringbufIcSt11char_traitsIcESaIcEE17_M_stringbuf_initESt13_Ios_Openmode',
    '_ZNSt15basic_stringbufIcSt11char_traitsIcESaIcEE6setbufEPci']))
