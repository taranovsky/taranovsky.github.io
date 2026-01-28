#!/usr/bin/python2 -i
"""Author: Dmytro Taranovsky    License: GPL 2 or later
This python module implements ordinal arithmetic using class Ordinal and its functions.
The module implements comparison, addition, multiplication, ordinal exponentiation, pretty printing, and other functions.
The easiest way to try out the module is by calling it from the interactive python interpreter:
For example, call "python -i OrdinalArithmetic.py", or if your system supports it, just execute OrdinalArithmetic.py to get a python prompt:
>>> 1+w*w+2+2  # w is the least infinite ordinal
w**2+4
>>> w**2 > w*5
True
>>> str(w)  # this shows the internal representation of the ordinal
'CC000'
>>> epsilon_0
phi(1,0)

Parts of this module are not optimized for speed; in particular, handling of large integers (such as 10000) is slow.

In the interactive mode, for more information about usage, you can use help(Ordinal).  You can also use help(<function>) for functions that are not methods of Ordinal such as CheckSyntax, StandardForm, Compare, OrdinalSum, SymmetricOrdinalSum, OrdinalProduct, phi_n.  The first three of these functions operate on strings.

The ordinal notation system (specifically, its internal representation), uses two constants: 0 and W, and a binary function C, with everything written in the prefix form.
For example, epsilon_0 == Ordinal("CCW00") == C(C(W, 0), 0).
Functions that operate on strings (including conversion from string to Ordinal) require this representation.

The ordinal representation system used here is the one described in the paper "Ordinal Notation" by Dmytro Taranovsky, specifically, the one in section "A Stronger Ordinal Notation".  For background, the reader is referred there.  However, for the basics on infinite ordinals, the reader is referred elsewhere.
"""

# Briefly, the notation system consists of 0, W (a large ordinal), and a binary function C.  For ordinals in the standard representation written in the postfix form, the comparison is done in the lexicographical order where 'C' < '0' < 'W':  For example, C(C(0,0),0) < C(W, 0) because 000CC < 0WC. (Note: This does not hold for non-standard representations of ordinals).  Of course, the real logic lies in deciding which representations are standard.  Here is a recursive definition.
# 1. '0' and 'W' are standard
# 2. If 'C(a,b)' is standard, then so are 'a' and 'b'.
# 3. If C('a', C('b', 'c')) is standard, then a<=b
# 4. If the above tests succeeded for "C(a,b)", then let T_a be the parse tree of 'a': T_a is the set of subterms of 'a', and for x and y in T_a, x<y means that y is a subterm of x and y!=x.  Let Ord(x) be the ordinal coded by x.  Parse 'a' into the set of terms below W. Formally,
# let X = {x in T_a: Ord(x) < W and forall y<x Ord(y)>=W}
# The test for the standard form is:
# forall x in X forall y>x (Ord(y)<Ord(x) or Ord(y)>=W or thereis z<=y Ord(z) < C(a, b))
# All comparisons between ordinals here can be done in the above-described lexicographical order.
#
# In addition to this definition, we mention some properties of C.
# If a is below the least fixpoint of x->omega^x above b, then C(a, b) = b + omega^a
# Let S_a be the closure of {y: y = C(a, x) for some x}
# C(a, b) is the least ordinal above b that is in S_a
# S_0 consists of all non-zero ordinals in the notation system.
# For limit a, S_a is the intersection of all S_b for b<a
# For every ordinal a, there is an ordinal b<=a such that
# S_{a+1} = lim(S_a) union (S_a intersect b)  (here lim(S_a) is the set of limit points of S_a).

usage = __doc__

import re, sys

def CheckSyntax(x):
	"""Return True x is a valid term and False otherwise."""
	n = 1 # n is the number of arguments that we expect to have
	if not isinstance(x, str):
		return False
	for i in range(len(x)):
		if x[i] not in ['0', 'W', 'C']:
			return False # invalid symbol
		if x[i] == 'C': n+=1
		else: n-=1
		if n == 0: # if we have the exact number of arguments, then return true iff we have reached the end of the string
			return i == len(x)-1
	return False # not enough arguments (or x is empty)

def CompareStd(x, y):
	"""A quick algorithm to compare x and y when they are both in the standard form"""
# If we read the string from right to left, then the comparison between ordinals
# in the standard representation is done in the lexicographic order with C < 0 < W
	x = ''.join(reversed(x))
	y = ''.join(reversed(y))
	return cmp(x.replace('0', 'O'), y.replace('0', 'O'))

def Arg(string, n, startindex=0):
# Assumption: string[startindex:] starts with a valid term x.
# if n = 0, return x
# if n = 1 and x is Cab, return a
# if n = 2 and x is Cab, return b
	nCs = 0 # number of 'C' that we have seen so far
	if n in (0, 1):
		start = startindex + n
	else:
		start = None
	for i in range(startindex, len(string)):
		if n == 2 and start is None and i == startindex + nCs*2 and i > startindex:
			start = i
		if (n != 1 and i == startindex + nCs*2 + 1) or (n == 1 and i == startindex + nCs*2 and i > startindex):
			return string[start:i]
		if string[i] == 'C':
			nCs+=1
	return string[start:]

# Convenient abbreviations
def a1(x): return Arg(x, 1)
def a2(x): return Arg(x, 2)

class ParseTree():
	"""Provides preorder right-to-left traversal of the parse tree of a valid term x.
	<string> is the ordinal term to be parsed, and <index> is the index (in <string>) of the start
	of the current subterm. <index> is -1 when the traversal has ended."""
	# Note: The user is responsible for ensuring that the requested operations are well-defined
	def __init__(self, string, index=0):
		self.string = string
		self.index = index
	def left_item(self):
		return self.index + 1
	def right_item(self):
		return self.index + 1 + len(Arg(self.string, 1, self.index))
	def parent_item(self):
		if self.index == 0:
			return -1
		nCs = 0
		for index in range(self.index-1, -1, -1):
			if self.string[index] == 'C':
				nCs+=1
			if self.index - index - nCs*2 <= 0:
				return index
	def go_left(self):
		self.index = self.left_item()
	def go_right(self):
		self.index = self.right_item()
	def go_up(self):
		self.index = self.parent_item()
	def term(self):
		"""Return the current term"""
		return Arg(self.string, 0, self.index)
	def next(self):
		"""Go to the next term in the right-to-left preorder traversal"""
		if self.string[self.index] == 'C':
			self.go_right()
		else:
			self.skip()
	def skip(self):
		"""Skip subterms of the current term, and go to the next term (in the right-to-left preorder traversal)"""
		index1 = self.index
		self.go_up()
		if self.index == -1:
			return
		while index1 == self.left_item():
			index1 = self.index
			self.go_up()
			if self.index == -1:
				return
		self.go_left()

def StandardForm(x, cache=None):
	"""Convert x to the standard form"""
	# We assume that x is a valid term
	# To speed up computation when we call the function multiple times, we keep a cache of the results
	if cache is None:
		cache = {}
	if x in cache:
		return cache[x]
	if x in ['0', 'W']:
		cache[x] = x
		return x
	a = StandardForm(a1(x), cache)
	b = StandardForm(a2(x), cache)
	while b not in ['0', 'W'] and CompareStd(a, a1(b)) == 1:
		b = a2(b) # recursively minimize b
	if a in ('0', 'W') or CompareStd(b, 'W') in (0, 1):
		cache[x] = 'C'+a+b
		return 'C'+a+b
	tree1 = ParseTree(a)
	# Parse 'a' in terms of ordinals d < Omega
	while tree1.term():
		d = tree1.term()
		if CompareStd(d, 'W') != -1:
			tree1.next()
			continue
		# Parse d in terms of ordinals e less than x
		tree2 = ParseTree(d)
		while tree2.term():
			e = tree2.term()
			if CompareStd(e, x) == -1:
				tree2.skip() # do not parse ordinals less than x
			elif CompareStd(e, 'W') == -1 and CompareStd(e, d) == 1:
				# Since d < e < Omega, a is not maximal
				# To maximize a, we replace e with Omega and remove all terms that are to the left of e
				# This works since we are traversing the tree from right to left.
				a = 'W' + a[tree1.index + tree2.index + len(e):]
				a = (len(a) - a.count('C')*2 - 1)*'C' + a
				a = StandardForm(a, cache) # this is necessary; an example is x='CCCW0CCW00CCW00'
				cache[x] = 'C'+a+b
				return 'C'+a+b
			else:
				tree2.next()
		tree1.skip()
	# At this point, a is maximal in C(a, b)
	cache[x] = 'C'+a+b
	return 'C'+a+b

def Compare(x, y, cache=None):
	"""Returns: -1 if x<y, 0 if x==y, 1 if x>y, and 2 if x or y is not a valid term"""
	# <cache> is the cache of results used by StandardForm"""
	if not CheckSyntax(x) or not CheckSyntax(y):
		return 2
	return CompareStd(StandardForm(x, cache), StandardForm(y, cache))


# Note:
# The code above defines the ordinal representation system.
# The code below creates class Ordinal to represent ordinals, and implements ordinal arithmetic.

class Ordinal(object):
	"""Implements ordinal arithmetic."""
	# Note:  Ordinals are essentially treated as immutable objects.

	def __init__(self, Input, **keys):
		# Input can be ordinal, string, or integer.
        # If nocheck keyword argument is true, then skip syntax check and conversion to standard form (to save compute); this assumes
		# that the Input is in the standard form.
		if type(Input) == type(1):
			if Input < 0:
				raise ValueError("Ordinals cannot be negative")
			self.string = 'C0'*Input+'0'
			return
		self.string = str(Input)
		if not isinstance(Input, Ordinal) and not ("nocheck" in keys and keys["nocheck"]):
			if not CheckSyntax(self.string):
				raise ValueError("Invalid syntax for ordinal representation")
			self.string = StandardForm(self.string)

	autoprettyprint = True # affects behavior of __repr__

	def __str__(self):
		return self.string

	def __repr__(self):
		"""if self.autoprettyprint is True (which is the default), then repr uses pretty printing, which is helpful for interactive use.
However, __str__ never uses pretty printing since we do not want to break Ordinal(str(self)) or otherwise make str unpredictable.
If self.autoprettyprint is False, then __repr__ is consistent with __str__ (and hence faster and more predictable).
To prevent repr from using pretty print by default, set Ordinal.autoprettyprint to False."""
		if self.autoprettyprint:
			if self.isinteger():
				return "Ordinal("+self.prettyprint()+")"
			return self.prettyprint()
		return "Ordinal('"+self.string+"')"

	def __cmp__(self, other):
		if not isinstance(other, Ordinal):
			other = Ordinal(other)
		return CompareStd(self.string, other.string)

	def __eq__(self, other):
		try:
			return self.string == Ordinal(other).string  # (this is faster than using cmp)
		except ValueError:
			return False

	def __ne__(self, other):
		return not self == other

	def __nonzero__(self):
		return self.string != '0'

	def isinteger(self):
		"""return True iff the ordinal is an integer"""
		return self < "CC000"

	def __int__(self):
		if not self.isinteger():
			raise ValueError("Not an integer")
		return self.string.count('C')

	def arg1(self):
		if self.string in ['0', 'W']:
			raise ValueError("Not a C-term")
		return Ordinal(a1(self.string), nocheck=True)

	def arg2(self):
		if self.string in ['0', 'W']:
			raise ValueError("Not a C-term")
		return Ordinal(a2(self.string), nocheck=True)

	def args(self):
		return self.arg1(), self.arg2()

	def C(self, other):
		return Ordinal('C'+self.string+Ordinal(other).string)

	def base_omega_fixpoint(self):
		"""return the largest fixpoint of x->omega^x that is not above self; return Ordinal(0) if self < epsilon_0"""
		answer = Ordinal(self) # Note:  Here, as elsewhere, it is important to return a copy of self instead of just self.
		while answer not in [0, 'W'] and answer.arg1() < answer:
			answer = answer.arg2()
		return answer

	def exp_omega(self):
		"""return omega^x"""
		fixpoint = self.base_omega_fixpoint()
		if fixpoint == self and fixpoint:
			return fixpoint
		else:
			return Ordinal('C'+self.string+fixpoint.string, nocheck=True)

	def decompose(self):
		"""return the standard additive decomposition of the ordinal"""
		return [x.exp_omega() for x in self.decompose2()]

	def decompose2(self):
		"""return [x1, x2, ...] where self = w**x1+w**x2+... and x1 >= x2 >= ..."""
		# An interesting note is that ordinary ordinal arithmetic can be implemented
		# just using this function, the inverse, and comparison for fixpoints of exponentiation base omega.
		if self == 0:
			return []
		fixpoint = self.base_omega_fixpoint()
		if fixpoint == self:
			return [fixpoint]
		decomposition = []
		arg = self
		while arg != fixpoint:
			decomposition.insert(0, arg.arg1())
			arg = arg.arg2()
		if decomposition[0] <= fixpoint and fixpoint:
			decomposition.insert(0, fixpoint)
		return decomposition

	def islimit(self):
		"""return True iff self is a limit ordinal"""
		if self == 0:
			return False
		return self == 'W' or self.arg1() > 0

	def ispowerofomega(self):
			"""return True iff self is a power of omega"""
			return len(self.decompose()) == 1

	def log_omega(self):
		"""return the largest y such that omega^y <= self"""
		if self == 0:
			raise ValueError("log_omega of 0 is not defined")
		return self.decompose2()[0]

	def __add__(self, other):
		return OrdinalSum(self, other)

	def __mul__(self, other):
		other = Ordinal(other)
		if other == 0:
			return Ordinal(0)
		elif other == 1:
			return Ordinal(self)
		list2 = other.decompose()
		if len(list2) != 1:
			return OrdinalSum(self*item for item in list2)
		# at this point, other is a nonzero power of omega
		# Note that (w^a+c)*w^b == w^(a+b) if b > 0 and c < w^(a+1).
		return (self.log_omega() + other.log_omega()).exp_omega()

	def __pow__(self, other):
		other = Ordinal(other)
		if other == 0 or self == 1:
			return Ordinal(1)
		elif other == 1:
			return Ordinal(self)
		elif self == 0:
			return Ordinal(0)
		list2 = other.decompose()
		if len(list2) != 1:
			return OrdinalProduct(self**item for item in list2)
		# at this point, other is a nonzero power of omega, and self > 1
		# Note that (w^a+c)^b == w^(a*b) if b is a limit ordinal and a > 0 and c < w^(a+1).
		if self.isinteger():
			if other == 'CC000':
				return Ordinal('CC000')
			else:
				return other.exp_omega()
		else:
			return (self.log_omega()*other).exp_omega()

	def __radd__(self, other):  return Ordinal(other)+self
	def __rmul__(self, other):  return Ordinal(other)*self
	def __rpow__(self, other):  return Ordinal(other)**self

	def leftsubtract(self, other):
		"""return x such that other+x == self"""
		other = Ordinal(other)
		if self < other:
			raise ValueError("ordinal values cannot be negative")
		list1 = self.decompose()
		list2 = other.decompose()
		cutoff = 0
		while cutoff < min(len(list1), len(list2)) and list1[cutoff] == list2[cutoff]:
			cutoff+=1
		return OrdinalSum(list1[cutoff:])

	def __floordiv__(self, other):
		"""return the maximum x such that other*x <= self"""
		other = Ordinal(other)
		if other == 0:
			raise ZeroDivisionError("ordinal division by 0")
		if self < other:
			return Ordinal(0)
		if other.ispowerofomega(): # this is just for efficiency; the code here is much faster for computing for example (w*100)/w
			decomp = self.decompose()
			end = len(decomp)
			while end > 0 and decomp[end-1] < other:
				end-=1
			return OrdinalSum(item.log_omega().leftsubtract(other.log_omega()).exp_omega() for item in decomp[:end])
		base_quotient = self.log_omega().leftsubtract(other.log_omega()).exp_omega()
		return base_quotient + self.leftsubtract(other*base_quotient)//other # recursive computation of quotient

	def __divmod__(self, other):
		"""return a, b such that self=other*a+b and b<other.
This corresponds to left division: x == y*(x/y) + x%y == y*x/y; because of lack of commutativity, x need not equal x*y/y."""
		other = Ordinal(other)
		quotient = self//other
		return quotient, self.leftsubtract(other*quotient)			

	def __rfloordiv__(self, other):  return Ordinal(other)//self
	__div__ = __floordiv__
	__rdiv__ = __rfloordiv__
	def __mod__(self, other):  return divmod(self, other)[1]
	def __rmod__(self, other):  return Ordinal(other) % self
	def __rdivmod__(self, other):  return divmod(Ordinal(other), self)

	def log(base, arg):
		"""return the largest y such that base**y <= arg"""
		arg = Ordinal(arg)
		if base < 2:
			raise ValueError("log base must be >1")
		if arg == 0:
			raise ValueError("log of 0 is not defined")
		if arg == 1:
			return Ordinal(0)
		if base == 'CC000':
			return arg.log_omega() # this is just for efficiency
		decomposition = arg.decompose()
		if len(decomposition) > 1:
			answer = base.log(decomposition[0])
			while base**(answer+1) <= arg:
				answer+=1
			return answer
		# at this point, arg is a nonzero power of omega
		if base.isinteger():
			return arg
		approximate_log = arg.log_omega() // base.log_omega()
		if base**approximate_log > arg: # this will only happen if base is not a power of omega
			return approximate_log.arg2() # Note: Here, approximate_log == approximate_log.arg2()+1.
		else:
			return approximate_log

	# Note:  While the functions above depend only on the general properties of C,
	# implementation of functions below partly depends on the exact definition of the standard form.

	def C_criticalsequence(self):
		"""Return ascending sequence S of ordinals such that x in S iff forall y<x self.C(y).arg1() > self.C(x).arg1()."""
		# The code assumes (and we conjecture) that all members of the sequence are subterms of self.
		# Notes about S:
		# * S[0] == 0
		# * self is maximal in "C(self, x)" iff x >= S[-1]
		def Cterms(x):
			# return the list of all terms in the representation of x
			if x in ['0', 'W']:
				return [x]
			return [x] + Cterms(x.arg1()) + Cterms(x.arg2())
		termlist = Cterms(self)
		cache = {}
		lastitem = None
		lastvalue = None
		seq = []
		for item in sorted(termlist + [Ordinal(0)]):
			if item == lastitem:
				continue  # this is just for efficiency
			lastitem = item
			if item.base_omega_fixpoint() != item:
				continue  # this is just for efficiency
			value = a1(StandardForm('C'+ self.string + item.string, cache))
			if value != lastvalue:
				seq.append(item)
			lastvalue = value
			if value == self:
				break # this is just for efficiency
		return seq

	def Citerate(self, count, base=0):
		"""Iterate x -> C(self, x) count number of times, starting at x=base, and return the resulting ordinal. count can be any ordinal."""
		count = Ordinal(count)
		base = Ordinal(base)
		if not count:
			return base
		if count == 1:
			return C(self, base)
		if self.base_omega_fixpoint() <= base:
			return base + self.exp_omega()*count
		if count >= 'W':
			 return self.Citerate(count.leftsubtract('W'), base='W') # this works since base < 'W' here
		if not count.ispowerofomega():
			result = base
			for cnt in count.decompose():
				result = self.Citerate(cnt, result)
			return result
		# Here count < 'W' and is a nonzero power of omega, and base < self.base_omega_fixpoint() (and hence base < 'W').
		# There are two possibilities: result equals count.base_omega_fixpoint(), and result > count.base_omega_fixpoint(), and we have to determine which.
		if count > base:
			seq = self.C_criticalsequence()
			crit_term = max(item for item in seq if item < count)
			self_max = C(self, crit_term).arg1() # self_max is maximized self in "C(self, x)" for x that are just below count
			if count.arg1() > self_max + count:
				return count
			# at this point, result > count.base_omega_fixpoint()
			base = max(base, count.base_omega_fixpoint())
		return C(C(self, base).arg1()+count.log_omega(), base)

	def phi(self, other):
		"""a.phi is the ath fixpoint function (with Ordinal(0).phi being exponentiation base w), and a.phi(b) is point b in the range of a.phi."""
		return phi_n(self, other)

	def phi_inv(base, arg):
		"""return the maximum x such that base.phi(x) <= arg; raise exception if arg < base.phi(0)"""
		arg = Ordinal(arg)
		if base == 0:
			return arg.log_omega()
		if arg < base or base > 'W':
			raise ValueError("Value too small for self.phi_inv(value) to be defined.")
		if arg >= 'W':
			return (Ordinal('W') if base < 'W' else Ordinal(0))
		# here 0 < base <= arg < 'W'
		A = C('W', arg) # next "admissible" ordinal above arg
		while arg and arg.arg1() < A*base:
			arg = arg.arg2()
		last_arg1 = None
		values = [] # the use of the values variable (as opposed to doing the summation incrementally) is for efficiency
		while arg and arg.arg1() < A*(base+1):
			if arg.arg1() != last_arg1: # the use of the if condition is for efficiency
				value = (arg.arg1() % A).exp_omega()
			last_arg1 = arg.arg1()
			values.append(value)
			arg = arg.arg2()
		result = OrdinalSum(reversed(values))
		if arg > base:
			result = arg + result
		elif arg == base:
			result = 1 + result
		if not result:
			raise ValueError("Value too small for self.phi_inv(value) to be defined.")
		return result.leftsubtract(1)

	def phi_args(self):
		"""if self is a power of omega, return the unique a,b such that self = phi(a, b) and b < self"""
		if not self.ispowerofomega():
			raise ValueError("Value must be a power of omega")
		if self == 'W':
			return Ordinal('W'), Ordinal(0)
		if self.arg1() < self:
			return Ordinal(0), self.arg1()
		A = C('W', self)
		a = self.arg1()//A
		if a >= A: # this is necessary and sufficient for self to be unreachable from below using phi
			return Ordinal(self), Ordinal(0)
		else:
			return a, a.phi_inv(self)

	def isbuiltfrombelow(self, x=0):
		"""Only defined for self < 'W'.  Return True iff the representation of self (using C) in terms of ordinals below x only uses ordinals below self, except for ordinals >= 'W'"""
		# Most of the code here is basically a copy of the relevant portion of StandardForm function
		if self >= 'W': # if self >= 'W', the correct behavior is not clear, so just raise an exception
			raise ValueError("isbuiltfrombelow is only defined when self < 'W'")
		d = self.string
		x = Ordinal(x).string
		tree2 = ParseTree(d)
		while tree2.term():
			e = tree2.term()
			if CompareStd(e, x) == -1:
				tree2.skip() # do not parse ordinals less than x
			elif CompareStd(e, 'W') == -1 and CompareStd(e, d) == 1:
				return False
			else:
				tree2.next()
		return True

	def prettyprint(self, **args):
		"""Print ordinal in a human-readable form
Behavior is configurable with keyword arguments.  For example, use poweroperator='^' to use '^' for power instead of the default '**'."""
		# Configurable parameters
		poweroperator = '**' # symbol for the power operator
		useextendedCNF = True # use multiplication; when appropriate, use Cantor normal form on bases >w.
		usephi = True # use the Veblen fixpoint functions
		context = None # the context in which the ordinal is used ('mul' -- '*', 'pow1' -- first argument of '**', 'pow2' -- second argument of '**'); this argument is used to automatically add external parentheses if necessary.
		if "poweroperator" in args: poweroperator = args["poweroperator"]
		if "useextendedCNF" in args: useextendedCNF = args["useextendedCNF"]
		if "usephi" in args: usephi = args["usephi"]
		if "context" in args:  context = args["context"]
		if self.isinteger():
			return str(int(self))
		elif self == 'W':
			return 'W'
		elif self == "CC000":
			return 'w'
		if self.base_omega_fixpoint() == self:
			args["context"] = None
			if usephi:
				a, b = self.phi_args()
				if a < self:
					return 'phi('+a.prettyprint(**args)+','+b.prettyprint(**args)+')'
			return 'C(' + self.arg1().prettyprint(**args) + ',' + self.arg2().prettyprint(**args) + ')'
		# Here the topmost operation is addition, multiplication, or power.
		decomp = self.decompose() # additive decomposition of the ordinal
		if useextendedCNF:  # combine terms as appropriate for the extended CNF.
			base = max(Ordinal('CC000'), self.base_omega_fixpoint())
			decomp2 = [[decomp[0]]]
			for i in range(1, len(decomp)):
				if decomp[i]*base > decomp[i-1]:
					decomp2[-1].append(decomp[i])
				else:
					decomp2.append([decomp[i]])
			decomp = [OrdinalSum(item) for item in decomp2]
		else:
			while len(decomp) > 1 and decomp[-2] == 1: # combine 1+1+...+1 into its sum
				decomp = decomp[:-2] + [decomp[-2]+decomp[-1]]
			if decomp[0].isinteger():
				return str(int(decomp[0]))
		if len(decomp) > 1:  # if the topmost operation is addition
			args["context"] = None
			answer = '+'.join(item.prettyprint(**args) for item in decomp)
			if context in ['mul', 'pow1', 'pow2']:
				answer = '('+answer+')'
			return answer
		if not useextendedCNF:
			# at this point, self is a power of omega
			args["context"] = 'pow2'
			answer = 'w' + poweroperator + self.log_omega().prettyprint(**args)
			if context == 'pow1':
				answer = '('+answer+')'
			return answer
		log = base.log(self)
		quotient = self//base**log # note that self % base**log == 0 here
		if quotient != 1: # if the topmost operation is multiplication
			args["context"]='mul'
			answer = (base**log).prettyprint(**args) + '*' + quotient.prettyprint(**args)
			if context in ['pow1', 'pow2']:
				answer = '('+answer+')'
			return answer
		# here the topmost operation is the power operation
		args["context"] = 'pow1'
		base_printed = base.prettyprint(**args)
		args["context"] = 'pow2'
		log_printed = log.prettyprint(**args)
		answer = base_printed + poweroperator + log_printed
		if context == 'pow1':
			answer = '('+answer+')'
		return answer


def OrdinalSum(*args):
	"""return the sum of its arguments; if there is just one argument, treat it as a list of ordinals to sum up"""
	# Note:  This function is used in the implementation of class Ordinal.
	# Note:  When there are many arguments, OrdinalSum is much faster than doing the sum by incremental addition.
	if len(args) == 1:
		args = args[0]
	decomposition = []
	for arg in args:
		decomposition+=Ordinal(arg).decompose2()
	max_arg = Ordinal(0)
	for i in range(len(decomposition)-1, -1, -1): # remove all terms from decomposition that do not increase the sum
		if decomposition[i] < max_arg:
			del decomposition[i]
		else:
			max_arg = decomposition[i]
	if not decomposition:
		return Ordinal(0)
	partial_answer = ''.join('C'+item.string for item in reversed(decomposition[1:]))
	fixpoint = decomposition[0].base_omega_fixpoint()
	if fixpoint == decomposition[0] and fixpoint:
		return Ordinal(partial_answer + fixpoint.string, nocheck=True)
	else:
		return Ordinal(partial_answer + 'C' + decomposition[0].string + fixpoint.string, nocheck=True)

def OrdinalProduct(*args):
	"""return the product of its arguments; if there is just one argument, treat it as a list of ordinals to process"""
	if len(args) == 1:
		args = args[0]
	product = Ordinal(1)
	for arg in args:
		product*=Ordinal(arg)
	return product

def SymmetricOrdinalSum(*args):
	"""return the symmetric (also called natural) sum of its arguments; if there is just one argument, treat it as a list of ordinals to process"""
	if len(args) == 1:
		args = args[0]
	decomposition = []
	for arg in args:
		decomposition+=Ordinal(arg).decompose()
	decomposition.sort(reverse=True) # this line is what makes the sum symmetric
	return OrdinalSum(decomposition)

def SymmetricOrdinalProduct(*args):
	"""return the symmetric (also called natural) product of its arguments; if there is just one argument, treat it as a list of ordinals to process"""
	if len(args) == 1:
		args = list(args[0])
	if len(args) == 0:
		return Ordinal(1)
	elif len(args) == 1:
		return Ordinal(args[0])
	elif len(args) > 2:
		return SymmetricOrdinalProduct(SymmetricOrdinalProduct(args[:-1]), args[-1])
	arg1 = Ordinal(args[0])
	arg2 = Ordinal(args[1])
	if arg1 == 0 or arg2 == 0:
		return Ordinal(0)
	if arg2 == 1:
		return arg1
	if arg1 == 1:
		return arg2
	if not arg2.ispowerofomega():
		return SymmetricOrdinalSum(SymmetricOrdinalProduct(arg1, arg) for arg in arg2.decompose())
	if not arg1.ispowerofomega():
		return SymmetricOrdinalSum(SymmetricOrdinalProduct(arg, arg2) for arg in arg1.decompose())
	return SymmetricOrdinalSum(arg1.log_omega(), arg2.log_omega()).exp_omega()

def phi_n(*args):
	"""n-variable Veblen fixpoint function: phi_n(c) = w^c; phi_n(b, c) = phi(b, c), phi(1, 0, c) = Gamma_{c}, and so on"""
	# this function is used to implement Ordinal.phi
	if len(args) == 0:
		raise ValueError("phi_n requires at least one argument")
	args = [Ordinal(arg) for arg in args]
	if OrdinalSum(args[:-1]) == 0:
		return args[-1].exp_omega()
	if max(args[:-1]) == 'W' and args[-1] == '0' or args[-1] == 'W' and max(args[:-1]) < 'W':
		return Ordinal('W')
	if max(args) >= 'W':
		raise ValueError("Result is too large to be representable")
	A = C('W', max(args)) # the least "admissible" ordinal above max(args).
	A_pred = max(args) # the predecessor admissible ordinal of A
	while A_pred and A_pred.arg1() < 'W':
		A_pred = A_pred.arg2()
	# note that A_pred <= max(args) < A
	degree = OrdinalSum(A**n*args[-n-1] for n in range(1, len(args)))
	base = max(A_pred, degree.C_criticalsequence()[-1])
	if max(args[:-1]) < base:
		count = args[-1].leftsubtract(base)
	elif max(args[:-1]) == base:
		count = args[-1]
	else:
		count = 1+args[-1]
	return degree.Citerate(count, base)

# useful ordinals
w = Ordinal('CC000')
W = Ordinal('W')
epsilon_0 = Ordinal('CCW00')
Gamma_0 = (Ordinal('CW0')**2).C(0)

def C(a, b):
	return Ordinal(a).C(b)

def phi(a, b):
	return Ordinal(a).phi(b)

if __name__ == "__main__" and len(sys.argv) >= 2 and sys.argv[1] in ['-h', '-help', '--help']:
	print usage
