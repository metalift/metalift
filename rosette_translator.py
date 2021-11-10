from analysis import CodeInfo, analyze
import ir
import re
import pyparsing as pp
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, Or, FnDecl, Var, Add, Ite, List, Bool, PrintMode, printMode
from llvmlite.binding import ValueRef

#param for bounding the input list length
n = 2

def generateAST(expr):
	s_expr = pp.nestedExpr(opener='(', closer=')')
	parser = pp.ZeroOrMore(s_expr)
	ast = parser.parseString(expr, parseAll=True).asList()
	return ast

def genVar(v, decls, vars_all):
	if v.type.name == "Int":
		decls.append("(define-symbolic %s integer?)"%(v))
		vars_all.append(v.args[0])
		
	elif v.type.name == "Bool":
		decls.append("(define-symbolic %s boolean?)"%(v))
		vars_all.append(v.args[0])
	
	elif v.type.name == "MLList":
		tmp = [v.args[0]+"_"+str(i) for i in range(n)]
		tmp.append(v.args[0]+'-len')
		vars_all = vars_all + tmp
		if v.type.args[0].name == "Int":
			decls.append("(define-symbolic %s integer?)"%(" ".join(tmp)))
			decls.append('(define %s (take %s %s))'%(v.args[0],"(list " + " ".join(tmp[:n]) + ")", tmp[-1]))
		elif v.type.args[0].name == "Bool":
			decls.append("(define-symbolic %s boolean?)"%(" ".join(tmp)))
			decls.append('(define %s (take %s %s))'%(v.args[0],"(list " + " ".join(tmp[:n]) + ")", tmp[-1]))
	elif v.type.name == "Tuple":
		elem_names = []
		for i, t in enumerate(v.type.args):
			elem_name = v.args[0] + "_" + str(i)
			genVar(Var(elem_name, t), decls, vars_all)
			elem_names.append(elem_name)

		# decls.append("(define %s (list %s))" % (v.args[0], " ".join(elem_names)))
	else:
		raise Exception(f"Unknown type: {v.type}")

def generateVars(vars):
	decls = []
	vars_all = []
	for v in list(vars):
		genVar(v, decls, vars_all)
		
	return "\n".join(decls),vars_all

def generateSynth(vars, invariant_guesses, loopAndPsInfo):
	
	listvars = "(list " + " ".join(vars) + ")"
	if invariant_guesses:
		blocking_constraints = []
		for inv in invariant_guesses:
			blocking_constraints.append("(assert (!(eq? inv %s)))"%(inv))
		asserts = " ".join(blocking_constraints)
		synth_fun = "(define sol\n (synthesize\n #:forall %s\n #:guarantee (begin (assertions) %s)))\n (sat? sol)\n %s"%(listvars,asserts, "(print-forms sol)")
	else:
		synth_fun = "(define sol\n (synthesize\n #:forall %s\n #:guarantee (assertions)))\n (sat? sol)\n %s"%(listvars,"(print-forms sol)")
	return synth_fun

def generateInvPs(loopAndPsInfo):
	
	decls = ""
	for i in loopAndPsInfo:
		all_args = i.readVars + i.modifiedVars if isinstance(i, CodeInfo) else i.args[2:]
		func_name = i.name if isinstance(i, CodeInfo) else i.args[0]
		arg_names = " ".join([a.name if isinstance(a, ValueRef) else str(a) for a in all_args])
		decls += "(define (%s %s) (%s %s #:depth 10))\n"%(func_name,arg_names,func_name+"_gram",arg_names)
	return decls			


def toRosette(filename,targetLang, vars, invAndPs, preds, vc, loopAndPsInfo, invGuess):

	f = open(filename,'w')
	print('#lang rosette\n(require "../utils/bounded.rkt")\n(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n\n',file=f)
	#structure for rosette functions
	print(open('./utils/utils.rkt','r').read(),file=f)

	#struct declarations and function definition of target constructs
	ir.printMode = PrintMode.RosetteVC
	
		
	for t in targetLang:
		if t.args[1] != "":
			print("\n",t,"\n",file=f)
	# print(generateInter(targetLang),file=f)
	
	#inv and ps grammar definition
	ir.printMode = PrintMode.RosetteVC
	for g in invAndPs:print(g,"\n",file=f)

	#inv and ps declaration
	print(generateInvPs(loopAndPsInfo),file=f)
	
	fnsDecls = []
	for t in targetLang:
		if t.args[1] == "":
			fnsDecls.append(t)
	if fnsDecls:
		print(generateInvPs(fnsDecls),file=f)
	
	#vars declaration 
	varDecls, vars_all = generateVars(vars)
	print(varDecls,file=f)

	#Vc definition
	print("(current-bitwidth %d)"%(6),file=f)
	ir.printMode = PrintMode.RosetteVC
	print("(define (assertions)\n (assert %s))\n"%(vc),file=f)

	#synthesis function
	print(generateSynth(vars_all,invGuess,loopAndPsInfo),file=f)
	f.close()


	# print(loopAndPsInfo)