import subprocess
import pyparsing as pp
import os
import ir
from ir import printMode,PrintMode
from ir import Expr, parseTypeRef, Constraint, MLInst_Assert, Call, FnDecl, Bool, Not, Add, Sub, Mul, Le, Lt, Ge, Gt, And, Or, Implies, Eq, Int, Bool, List, Ite, IntLit, BoolLit, MakeTuple
from rosette_translator import toRosette



#utils for converting rosette output to IR
def generateAST(expr):
	s_expr = pp.nestedExpr(opener='(', closer=')')
	parser = pp.ZeroOrMore(s_expr)
	ast = parser.parseString(expr, parseAll=True).asList()
	return ast

def stringToIr(sols, loopAndPsInfo, fnsType):
	candidates = []
	for idx,s in enumerate(sols):
		locMappings = {}
		for idx,v in enumerate(loopAndPsInfo[idx].modifiedVars + list(loopAndPsInfo[idx].readVars)):
			if isinstance(v, Expr) and v.kind == Expr.Kind.Var:
				locMappings['(loc %d)'%(idx)] = v.args[0]
			else:
				locMappings['(loc %d)'%(idx)] = v.name
		for key in locMappings.keys():
			s = s.replace(key,locMappings[key])
		ast = generateAST(s)
		for a in ast:
			expr = toExpr(a,fnsType)
		ir.printMode = PrintMode.SMT
		candidates.append(expr)
	return candidates

def toExpr(ast,fnsType):

	expr_bi = {'_eq': Eq, '_add': Add, '_sub': Sub, '_mul': Mul, '_lt': Lt, '_lte': Le, '_gt': Gt, '_gte':  Ge,'_and':  And, '_or':  Or, '=>':  Implies}
	expr_uni = {'_not': Not}

	if ast[0] in expr_bi.keys():
		return expr_bi[ast[0]](toExpr(ast[1],fnsType), toExpr(ast[2],fnsType))
	elif ast[0] in expr_uni.keys():
		return expr_uni[ast[0]](toExpr(ast[1]),fnsType)
	elif ast[0] == '_if' or ast[0] == 'ite':
		return Ite(toExpr(ast[1],fnsType), toExpr(ast[2],fnsType), toExpr(ast[3],fnsType))
	elif ast[0] == '_list_length':
		return Call("list_length", Int(), toExpr(ast[1],fnsType))
	elif ast[0] == '_list_eq':
		return Call("=", Bool(), toExpr(ast[1],fnsType), toExpr(ast[2],fnsType))
	elif ast[0] == '_list-append':
		return Call("list_append", List(Int()), toExpr(ast[1],fnsType), toExpr(ast[2],fnsType) )
	elif ast[0] == '_list_tail':
		return Call("list_tail", List(Int()), toExpr(ast[1],fnsType), toExpr(ast[2],fnsType) )
	elif ast[0] == '_list_concat':
		return Call("list_concat", List(Int()), toExpr(ast[1],fnsType), toExpr(ast[2],fnsType) )
	elif ast[0] == '_list_concat':
		return Call("list_concat", List(Int()), toExpr(ast[1],fnsType), toExpr(ast[2],fnsType) )
	# elif ast[0] == '_tuple_n':
	# 	index = toExpr(ast[2],fnsType)
	# 	if index.kind == Expr.Kind.Ite and index.args[0].kind == Expr.Kind.Lit:
	# 		if index.args[0].args[0]:
	# 			index = index.args[2]
	# 		else:
	# 			index = index.args[1]
	# 	return Expr(Expr.Kind.TupleSel, Int(), [toExpr(ast[1],fnsType), index])
	# elif ast[0] == "list":
	# 	return MakeTuple(*[toExpr(e,fnsType) for e in ast[1:]])
	elif ast[0].startswith('_'):
		
		arg_eval =[]
		for alen in range(1,len(ast)):
			arg_eval.append(toExpr(ast[alen],fnsType))
		retT = fnsType[ast[0]]

		return Call(ast[0][1:], retT, *arg_eval)
	else:
		if ast.isnumeric():
			return IntLit(ast)
		else:
			# if ast.split('$')[0] == "0":
			# 	return BoolLit(True)
			# else:
			# 	return ast.split('$')[0]
			return ast
def generateTypes(lang):
	fnsType = {}
	for l in lang:
		fnsType['_'+l.args[0]] = l.type
	return fnsType
def synthesize(basename,lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath):
	invGuess = []
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)

	while(True):
		synthFile = synthDir + basename + '.rkt'
		toRosette(synthFile,lang,vars, invAndPs, preds, vc, loopAndPsInfo,invGuess)
		procSynthesis = subprocess.run(["racket",synthFile],stdout=subprocess.PIPE)
		resultSynth = procSynthesis.stdout.decode("utf-8").split("\n")
		resultSynth.remove('')
		if resultSynth[0] == "#t":
			for idx,res in enumerate(resultSynth[1:len(resultSynth)-1]):
				print("Generated Inv%d %s"%(idx,res))
			print("Generated Program Summary %s"%(resultSynth[-1]))
		fnsType = generateTypes(lang)
		
		candidates = stringToIr(resultSynth[1:],loopAndPsInfo,fnsType)

		candidatesSMT = []
		for idx,ce in enumerate(loopAndPsInfo):
		
			
			candidatesSMT.append(FnDecl(ce.name, ce.retT, candidates[idx],*ce.modifiedVars, *ce.readVars))
		print("====== verification")
		verifFile = synthDir + basename + '.smt'
		
		toSMT(lang,vars,candidatesSMT,preds,vc, verifFile)


		procVerify = subprocess.run([cvcPath,'--lang=smt','--tlimit=100000',verifFile],stdout=subprocess.PIPE)

		if procVerify.returncode < 0:
			resultVerify = "SAT/UNKNOW"
		else:
			procOutput = procVerify.stdout
			resultVerify = procOutput.decode("utf-8").split("\n")[0]

		print("Vefication Output ", resultVerify)
		if resultVerify == "unsat":
			print("Candidates Verified")
			break
		else:
			print("verification failed")
			invGuess.append(resultSynth[1])
			print(invGuess)
			raise Exception()

	return candidatesSMT

def toSMT(targetLang, vars, invAndPs, preds, vc, outFile):
	# order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
	with open(outFile, mode="w") as out:
		if 'list' in outFile:
			out.write(open("./utils/list-axioms.smt",'r').read())
		out.write("\n\n".join([str(t) for t in targetLang]))

		out.write("\n\n".join(["\n%s\n"%(cand) for cand in invAndPs]))
		# out.write("\n\n%s\n\n" % invAndPs)

		v = "\n".join(["(declare-const %s %s)" % (v.args[0], v.type) for v in vars])  # name and type
		out.write("\n%s\n\n" % v)

		if isinstance(preds, str):
			out.write("%s\n\n" % preds)

		# a list of Exprs - print name, args, return type
		elif isinstance(preds, list):
			preds = "\n".join(["(define-fun %s (%s) (%s) )" %
										    (p.args[0], " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]), p.type)
										    for p in preds])
			out.write("%s\n\n" % preds)

		else: raise Exception("unknown type passed in for preds: %s" % preds)


		out.write("%s\n\n" % MLInst_Assert(Not(vc)))
		out.write("(check-sat)\n(get-model)")
