import subprocess
import pyparsing as pp
import os

from ir import Expr, parseTypeRef, Constraint, Assert, Pred


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

def extractFuns(funDef):
	funDecls, funName, returnType = [], [], []
	ast = generateAST(funDef)
	for a in ast:
		if 'define-fun-rec' in a:
			funDecls.append('( ' + ' '.join(list(flatten(a))) + ' )')
			funName.append(a[1])
			returnType.append(a[3])
	return funDecls, funName, returnType

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

def toExpr(ast, funName, returnType):
	expr_bi = {'=':Expr.Eq, '+':Expr.Add, '-':Expr.Sub, '<':Expr.Lt, '<=':Expr.Le, '>':Expr.Gt, '>=': Expr.Ge,'and': Expr.And, 'or': Expr.Or, '=>': Expr.Implies}
	expr_uni = {'not':Expr.Not}
	if ast[0] in expr_bi.keys():
		return expr_bi[ast[0]](toExpr(ast[1], funName, returnType) , toExpr(ast[2], funName, returnType))
	elif ast[0] in expr_uni.keys():
		return expr_uni[ast[0]](toExpr(ast[1], funName, returnType))
	elif ast[0] in funName:
		index = funName.index(ast[0])
		return Pred(ast[0],returnType[index] , toExpr(ast[1], funName, returnType))
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



def synthesize_new(targetLang, invAndPs, vars, preds, vc, cvcPath, basename):
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)
	sygusFile = synthDir + basename + ".sl"

	# Generate sygus file for synthesis
	toSMT(targetLang, "\n\n".join([str(i) for i in invAndPs]), vars, preds, vc, sygusFile, True)

	# logfile = synthDir + basename + '_logs.txt'
	# synthLogs = open(logfile, 'a')
	# # Run synthesis subprocess
	# proc = subprocess.Popen([cvcPath, '--lang=sygus2', '--output=sygus', sygusFile],
	# 												stdout=synthLogs)  # ,stderr=subprocess.DEVNULL)
	#
	# funDecls, funName, returnType = extractFuns(funDef)
	# funs = "\n".join(d for d in funDecls)
	# synthDecls = generateDecls(loopInfo)
	# logfileVerif = open(logfile, "r")
	# while True:
	# 	line = logfileVerif.readline()
	# 	if 'sygus-candidate' in line:
	# 		print("Current PS and INV Guess ", line)
	# 		candidates = "\n".join(d for d in generateCand(synthDecls, line, funName, returnType))
	# 		smtFile = synthDir + basename + ".smt"
	# 		toSMT(funs, vars, candidates, vc, smtFile, False)
	#
	# 		# run external verification subprocess
	# 		procVerify = subprocess.Popen([cvcPath, '--lang=smt', '--fmf-fun', '--tlimit=10000', smtFile],
	# 																	stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
	# 		output = procVerify.stdout.readline()
	# 		output = output.decode("utf-8")
	# 		if output.count('unsat') == 1:
	# 			print("UNSAT\n")
	# 			print("Verified PS and INV Candidates ", candidates)
	# 			break
	# 		else:
	# 			print("CVC4 verification Result for Current Guess")
	# 			print("SAT\n")


# print to a file
def toSMT(targetLang, invAndPs, vars, preds, vc, outFile, isSynthesis):
	# order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
	with open(outFile, mode="w") as out:
		out.write(targetLang)

		out.write("%s\n\n" % invAndPs)

		v = "\n".join(["(declare-const %s %s)" % (v.args[0], v.type) for v in vars])  # name and type
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
			out.write("%s\n\n" % Assert(Expr.Not(vc)))
			out.write("(check-sat)\n(get-model)")
