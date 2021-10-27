import subprocess
import pyparsing as pp
import os

from ir import Expr, parseTypeRef, Constraint, MLInst_Assert, Call, FnDecl, Bool, Not, Add, Sub, Mul, Le, Lt, Ge, Gt, And, Or, Implies, Eq, TupleSel, Int


def flatten(L):
	for l in L:
		if isinstance(l,list):
			yield "("
			yield from flatten(l)
			yield ")"
		else:
			yield l

def generateAST(expr):
	s_expr = pp.nestedExpr(opener='(', closer=')')
	parser = pp.ZeroOrMore(pp.Suppress('(exit)') | s_expr)
	ast = parser.parseString(expr, parseAll=True).asList()
	return ast

def extractFuns(targetLang):
	funName, returnType = [], [],
	for t in targetLang:
		funName.append(t.args[0])
		returnType.append(t.type)
	return funName, returnType

def generateDecls(loopInfo):
	invpsDecls = {}
	for l in loopInfo:
		funName = '(define-fun ' + l.name + '('
		for h in l.modifiedVars:
			funName += '( ' + h.name + " " + str(parseTypeRef(h.type)) + ' ) '
		for f in l.readVars:
			funName += '( ' + f.name + " " + str(parseTypeRef(f.type)) + ' ) '
		funName += ') Bool '
		invpsDecls[l.name] = funName
	return invpsDecls

def generateCand(synthDecls, line, funName, returnType):
	candidates, candidatesExpr = [], {}
	ast  = generateAST(line)
	for k in synthDecls.keys():
		for a in ast[0]:
			if k in a:
				candidatesExpr[a[0]] = toExpr(a[1],funName, returnType)
				candidates.append(synthDecls[k] + ' ('  + ' '.join(list(flatten(a[1]))) + '))')
	return candidates

def generateCandidates(invAndPs, line, funName, returnType):
	candidates, candidatesExpr = [], {}
	ast  = generateAST(line)
	for ce in invAndPs:
		name = ce.args[0]
		for a in ast[0]:
			if name in a:
				candidatesExpr[a[0]] = toExpr(a[1],funName, returnType)
				candidates.append(FnDecl(ce.args[0], ce.type, '(' +  ' '.join(list(flatten(a[1]))) + ')', *ce.args[2:]))
	return candidates, candidatesExpr

def toExpr(ast, funName, returnType):
	expr_bi = {'=': Eq, '+': Add, '-': Sub, '*': Mul, '<': Lt, '<=': Le, '>': Gt, '>=':  Ge,'and':  And, 'or':  Or, '=>':  Implies}
	expr_uni = {'not': Not}
	if type(ast[0]) == list and ast[0][0] == "_" and ast[0][1] == "tuple_select":
		return "TODO"
	elif ast[0] in expr_bi.keys():
		return expr_bi[ast[0]](toExpr(ast[1], funName, returnType) , toExpr(ast[2], funName, returnType))
	elif ast[0] in expr_uni.keys():
		return expr_uni[ast[0]](toExpr(ast[1], funName, returnType))
	elif ast[0] in funName:
		index = funName.index(ast[0])
		return Call(ast[0], returnType[index], toExpr(ast[1], funName, returnType))
	else:
		return ast

def callCVC(funDef, vars, loopInfo, preds, vc, cvcPath, basename):
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)
	sygusFile = synthDir + basename + ".sl"

	# Generate sygus file for synthesis
	toSMT("", funDef, vars, preds, vc, sygusFile, True)

	logfile = synthDir + basename + '_logs.txt'
	synthLogs = open(logfile,'a')
	#Run synthesis subprocess
	proc = subprocess.Popen([cvcPath, '--lang=sygus2', '--output=sygus' ,  sygusFile],stdout=synthLogs)#,stderr=subprocess.DEVNULL)

	funDecls, funName, returnType = extractFuns(funDef)
	funs = "\n".join(d for d in funDecls)
	synthDecls = generateDecls(loopInfo)
	logfileVerif = open(logfile,"r")
	while True:
		line = logfileVerif.readline()
		if 'sygus-candidate' in line:
			print("Current PS and INV Guess ", line)
			candidates = "\n".join(d for d in generateCand(synthDecls, line, funName, returnType))
			smtFile = synthDir + basename + ".smt"
			toSMT(funs, vars, candidates, vc, smtFile, False)

			#run external verification subprocess
			procVerify = subprocess.Popen([cvcPath, '--lang=smt', '--fmf-fun', '--tlimit=10000' ,  smtFile],stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
			output = procVerify.stdout.readline()
			output = output.decode("utf-8")
			if output.count('unsat') == 1:
				print("UNSAT\n")
				print("Verified PS and INV Candidates ", candidates)
				break
			else:
				print("CVC4 verification Result for Current Guess")
				print("SAT\n")


def synthesize(invAndPs, vars, preds, vc, ansFile, cvcPath, basename):
	grammars = open(ansFile, mode="r").read()

	callCVC(grammars, vars, invAndPs, preds, vc, cvcPath, basename)



def synthesize_new(basename, targetLang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath):
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)
	sygusFile = synthDir + basename + ".sl"

	# Generate sygus file for synthesis
	toSMT(targetLang, "\n\n".join([str(i) for i in invAndPs]), vars, preds, vc, sygusFile, True)

	logfile = synthDir + basename + '_logs.txt'
	synthLogs = open(logfile, 'w')
	# Run synthesis subprocess
	proc = subprocess.Popen([cvcPath, '--lang=sygus2', '--output=sygus', '--no-sygus-pbe', sygusFile],
													stdout=synthLogs)  # ,stderr=subprocess.DEVNULL)

	funName, returnType = extractFuns(targetLang)
	logfileVerif = open(logfile, "r")
	while True:
		line = logfileVerif.readline()
		if 'fail' in line:
			print("SyGuS failed")
			break
		elif 'sygus-candidate' in line:
			print("Current PS and INV Guess ", line)
			candidates, _ = generateCandidates(invAndPs, line, funName, returnType)
			candDef = "\n\n".join(str(d) for d in candidates)
			smtFile = synthDir + basename + ".smt"
			toSMT(targetLang, candDef, vars, preds, vc, smtFile, False)

			# run external verification subprocess
			procVerify = subprocess.Popen([cvcPath, '--lang=smt', '--fmf-fun', '--tlimit=10000', smtFile],
																		stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
			output = procVerify.stdout.readline()
			output = output.decode("utf-8")
			if output.count('unsat') == 1:
				print("UNSAT\n")
				print("Verified PS and INV Candidates ", candDef)

				return candidates

			else:
				print("CVC4 verification Result for Current Guess")
				print("SAT\n")


# print to a file
def toSMT(targetLang, invAndPs, vars, preds, vc, outFile, isSynthesis):
	# order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
	with open(outFile, mode="w") as out:
		out.write("\n\n".join([str(t) for t in targetLang]))

		out.write("\n\n%s\n\n" % invAndPs)

		var_decl_command = "declare-var" if isSynthesis else "declare-const"
		v = "\n".join(["(%s %s %s)" % (var_decl_command, v.args[0], v.type) for v in vars])  # name and type
		out.write("%s\n\n" % v)

		if isinstance(preds, str):
			out.write("%s\n\n" % preds)

		# a list of Exprs - print name, args, return type
		elif isinstance(preds, list):
			preds = "\n".join(["(define-fun %s (%s) (%s) )" %
										    (p.args[0], " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]), p.type)
										    for p in preds])
			out.write("%s\n\n" % preds)

		else: raise Exception("unknown type passed in for preds: %s" % preds)

		if isSynthesis:
			out.write("%s\n\n" % Constraint(vc))
			out.write("(check-synth)")
		else:
			out.write("%s\n\n" % MLInst_Assert(Not(vc)))
			out.write("(check-sat)\n(get-model)")
