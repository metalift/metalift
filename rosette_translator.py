from analysis import CodeInfo, analyze
import ir
import re
import pyparsing as pp
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, Or, FnDecl, Var, Add, Ite, List, Bool, PrintMode, printMode

#param for bounding the input list length
n = 2

def generateAST(expr):
	s_expr = pp.nestedExpr(opener='(', closer=')')
	parser = pp.ZeroOrMore(s_expr)
	ast = parser.parseString(expr, parseAll=True).asList()
	return ast

def generateVars(vars):
	decls = ""
	vars_all = []
	for v in list(vars):
		if v.type.name == "Int":
			decls += "(define-symbolic %s integer?)\n"%(v)
			vars_all.append(v.args[0])
			
		elif v.type.name == "Bool":
			decls += "(define-symbolic %s boolean?)\n"%(v)
			vars_all.append(v.args[0])
		
		elif v.type.name == "MLList":
			tmp = [v.args[0]+"_"+str(i) for i in range(n)]
			tmp.append(v.args[0]+'-len')
			vars_all = vars_all + tmp
			if v.type.args[0].name == "Int":
				decls += "(define-symbolic %s integer?)\n"%(" ".join(tmp))
				decls += '(define %s (take %s %s))\n'%(v.args[0],"(list " + " ".join(tmp[:n]) + ")", tmp[-1])
			elif v.type.args[0].name == "Bool":
				decls += "(define-symbolic %s boolean?)\n"%(" ".join(tmp))
				decls += '(define %s (take %s %s))\n'%(v.args[0],"(list " + " ".join(tmp[:n]) + ")", tmp[-1])
	return decls,vars_all
def generateSynth(vars, invariant_guesses, loopAndPsInfo):
	
	listvars = "(list " + " ".join(vars) + ")"
	if invariant_guesses:
		blocking_constraints = []
		for inv in invariant_guesses:
			blocking_constraints.append("(assert (!(eq? inv %s)))"%(inv))
		asserts = " ".join(blocking_constraints)
		synth_fun = "(define sol\n (synthesize\n #:forall %s\n #:guarantee (begin (assertions) %s)))\n (sat? sol)\n %s"%(listvars,asserts, "\n".join(["(evaluate %s sol)"%(a.name) for a in loopAndPsInfo]))
	else:
		synth_fun = "(define sol\n (synthesize\n #:forall %s\n #:guarantee (assertions)))\n (sat? sol)\n %s"%(listvars,"\n".join(["(evaluate %s sol)"%(a.name) for a in loopAndPsInfo]))
	return synth_fun

def generateStruct(FnDecl):
	structDecl = "(struct _%s (%s) #:transparent)"%(str(FnDecl.args[0]), ' '.join([f.args[0] if f.type.name == "Function" else str(f) for f in FnDecl.args[2:]]))
	return structDecl

def generateInter(FnDecl):
	interpreter = "(define (interpret2 e env)\n(match e\n"
	for fns in FnDecl:
		interpreter += '[(_%s %s) (%s %s)]\n'%(str(fns.args[0]), ' '.join([f.args[0] if f.type.name == "Function" else str(f) for f in fns.args[2:]]),str(fns.args[0]),' '.join(["(interpret %s env)"%(v) if v.type.name != "Function" else "%s"%(v.args[0])  for v in fns.args[2:]])) 
	#base case
	interpreter += '[_ e]))\n\n'
	return interpreter
def generateInvPs(loopAndPsInfo):
	decls = ""
	for i in loopAndPsInfo:
		decls += "(define %s (%s %s #:depth 10))\n"%(i.name,i.name+"_gram"," ".join(["(loc %d)"%(idx) for idx in range(len(i.readVars)+len(i.modifiedVars))]))
	return decls			


def toRosette(filename,targetLang, vars, invAndPs, preds, vc, loopAndPsInfo, invGuess):

	f = open(filename,'w')
	print('#lang rosette\n(require "../utils/bounded.rkt")\n(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n\n',file=f)
	#structure for rosette functions
	print(open('./utils/utils.rkt','r').read(),file=f)

	#struct declarations and function definition of target constructs
	ir.printMode = PrintMode.RosetteVC
	
		
	for t in targetLang:print("\n",generateStruct(t),"\n",t,"\n",file=f)
	print(generateInter(targetLang),file=f)
	
	#inv and ps grammar definition
	ir.printMode = PrintMode.Rosette
	for g in invAndPs:print(g,"\n",file=f)

	#inv and ps declaration
	print(generateInvPs(loopAndPsInfo),file=f)
	
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