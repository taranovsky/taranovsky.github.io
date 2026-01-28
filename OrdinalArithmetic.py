#!/usr/bin/python -i
# This module works with both python 2 and python 3.

"""Author: Dmytro Taranovsky    License: GPL 2 or later
Last Modified:  August 31, 2016
This python module implements ordinal arithmetic using class Ordinal and its functions.
The module implements comparison, addition, multiplication, ordinal exponentiation, pretty printing, and other functions.
The easiest way to try out the module is by calling it from the interactive python interpreter:
For example, call "python -i OrdinalArithmetic.py" (note the "-i"; "python OrdinalArithmetic.py" would not do much). 
Alternatively, if your system supports it, just execute OrdinalArithmetic.py to get a python prompt:
>>> 1+w*w+2+2  # w is the least infinite ordinal
w**2+4
>>> w**2 > w*5
True
>>> w.data  # this shows the internal representation of the ordinal
(1,1,0)
>>> epsilon_0
phi(1,0)
>>> epsilon_1=phi(1,1); Ordinal.symbols[epsilon_1]="epsilon_1"; print epsilon_1+epsilon_1  # Ordinal.symbols affects how ordinals are printed; see prettyprint documentation for more details
epsilon_1*2

You can can use "pydoc OrdinalArithmetic" to see the module documentation, or in the interactive mode, for more information about usage, you can use help(Ordinal).  You can also use help(<function>) for functions that are not methods of Ordinal such as CheckSyntax, StandardForm, CompareStd, OrdinalSum, SymmetricOrdinalSum, OrdinalProduct, SymmetricOrdinalProduct, phi_n, phi_extended (use dir() to get complete listing).

The ordinal notation system (specifically, its internal representation, which is stored in the data attribute), uses constants 0, 'W', 'WW', 'WWW', ..., and a binary function C2.  C2(a, b) is stored as (1, a, b), and for exponential reduction of size, we use (n+1, a, b) (displayed like Cn(n+1, a, b)) for (1, a, (n, a, b)).  The displayed representation is different and uses integers, 'w', '+','*','**', 'W', 'C', 'phi' (and optionally 'wCK'). C is monotonic and continuous and C(w**a_n+...w**a_2+w**a_1) = C2(a_1,C2(a_2,... C2(a_n,0)..)) provided that each a_i is maximal.

For example, epsilon_0 == phi(1,0) == Ordinal((1, 'W', 0)) == C2(W(1), 0) == C(W(1)) == C(wCK(1)).

The ordinal representation system used here is the one described in the paper "Ordinal Notation" by Dmytro Taranovsky and is conjectured to reach full second order arithmetic or even further.  For background, the reader is referred there.  However, for the basics on infinite ordinals, the reader is referred to another text.
Notational Difference:  The module uses "C2" for what the paper (as of early 2013) calls 2-variable C; C2(a,b) = C(Cinv(b)+w**a).
"""
# Here is a brief but complete description of the notation system:
#
# Definition: An ordinal a is 0-built from below from <b iff a<b
# a is n+1-built from below from <b iff the standard representation of a does not use ordinals above a except in the scope of an ordinal n-built from below from <b. 
#
# The nth (n is a positive integer) ordinal notation system is defined as follows.
#
# Syntax: Two constants (0, W_n) and a binary function C2 (corresponds to C in my paper (at least as of early 2013)).
# Comparison: For ordinals in the standard representation written in the postfix form, the comparison is done in the lexicographical order where 'C2' < '0' < 'W_n': For example, C2(C2(0,0),0) < C2(W_n, 0) because 0 0 0 C2 C2 < 0 W_n C2.
#
# Standard Form:
# 0, W_n are standard
# "C2(a, b)" is standard iff
# 1. "a" and "b" are standard,
# 2. b is 0 or W_n or "C2(c, d)" with a<=c, and
# 3. a in n-built from below from <C(a,b) (use the comparison above to check).
#
# The full notation system is obtained by combining these notation systems:
# Constants 0 and W_i (for every positive integer i), and binary function C.
# W_i = C2(W_{i+1}, 0) and the standard form always uses W_i instead of C2(W_{i+1}, 0).
# To check for standard form and compare ordinals, use W_i = C2(W_{i+1}, 0) to convert each W to W_n for a single positive integer n (it does not matter which n) and then use the nth ordinal notation system.
#
#
# In addition to this definition, we mention some properties of C2.
# If a is below the least fixpoint of x->omega^x above b, then C2(a, b) = b + omega^a
# Let S_a be the closure of {y: y = C2(a, x) for some x}
# C2(a, b) is the least ordinal above b that is in S_a
# S_0 consists of all non-zero ordinals in the notation system.
# For limit a, S_a is the intersection of all S_b for b<a
# For every ordinal a, there is an ordinal b<=a such that
# S_{a+1} = lim(S_a) union (S_a intersect b)  (here lim(S_a) is the set of limit points of S_a).
#
# In the program, the shorthand Cn(n, a, b) (described in the doc string above) is used iff the expansion would result in a standard form.  W(i) is W_i.
# Originally, the program was developed using C2 instead of C (hence extensive usage of C2 internally), but using C result in much more readable representations.
# C2 is used instead 2-argument C to avoid confusion between C(a, base=b) and C2(a,b).
#
# Version History:
# June 30, 2009:  Comparison algorithm for a system closely resembling n=2 system.
# November 29, 2010:  Implemented ordinal arithmetic that system.
# March 19, 2012:  Extended the script to (conjectured) full second order arithmetic (or even further); exponential space and time reduction in handling of large integers and n-iteration for large n; added several new functions.  This involved rewriting the first half of the script, and extensively modifying class Ordinal.
# February 23, 2013: Support python 3.
# March 3, 2013: Added one variable collapsing function and use it by default in prettyprint.
# March 13, 2015: Added Ordinal.symbols to allow shorter customizable ordinal representations.
# August 31, 2016:  Allow a in C(a,b) be n-built from below from <C(a,b) rather than from <=b.

import sys

type_long = type(2**256) # workaround for long integers not being int in python 2

def CheckSyntax(a):
	"""return True if a has the right syntactic form in our representation of ordinals"""
	if isinstance(a, int) or isinstance(a, type_long):
		return a >= 0
	if isinstance(a, str):
		return len(a) > 0 and a == 'W'*len(a)
	if isinstance(a, tuple):
		return len(a) == 3 and (isinstance(a[0], int) or isinstance(a[0], type_long)) and a[0] >= 0 and CheckSyntax(a[1]) and CheckSyntax(a[2])
	return False # wrong type

def MaxOmegaUsed(a):
	"""returns the maximum i such that a uses W_i"""
	if a == 0:
		return 0
	if isinstance(a, str):
		return len(a)
	return max(MaxOmegaUsed(a[1]), MaxOmegaUsed(a[2]))

# There are multiple choices about how different W_i are combined, and how to store (finite) iterations of C.
# We could have retained lexicographical comparison in the full system by using C2(a, W_i) in place of C2(a, 0) where C2(a, W_i) == C2(a, 0) and i is the largest possible.  However, as it stands, we rely on ChangeOmegaN for comparison.
def ChangeOmegaN(a, n):
	"""n=0 -- minimize i in each W_i used; n>0 -- for all i<n, replace each W_i with the right expression using W_n; return the result"""
	if n == 0:
		if not isinstance(a, tuple):
			return a
		a = (a[0], ChangeOmegaN(a[1], 0), ChangeOmegaN(a[2], 0))
		if isinstance(a[1], str) and len(a[1]) > 1 and a[2] == 0:
			if a[0] == 1:
				return 'W'*(len(a[1])-1)  # convert C2(W_{i+1}, 0) to W_i
			return (a[0]-1, a[1], 'W'*(len(a[1])-1)) # convert Cn(n+1, W_{i+1}, 0) to Cn(n, W_{i+1}, W_i) per our convention (expansion of Cn must result in standard form)
		return a
	if a == 0 or isinstance(a, str) and len(a) >= n:
		return a
	if isinstance(a, str): # convert W_i to C..C2(W_n, 0),..,0)
		b = 'W'*n
		for i in range(n-len(a)):
			b = (1, b, 0)
		return b
	if isinstance(a[1], str) and isinstance(a[2], str) and len(a[2]) == len(a[1])-1: # correct handling of C2(n, W_{i+1}, W_i)
		a = (a[0]+1, a[1], 0)
	return (a[0], ChangeOmegaN(a[1], n), ChangeOmegaN(a[2], n))

def ConvertToList(a):
	"""convert ordinal a to a list of integers and strings"""
	if not isinstance(a, tuple):
		return (a,)
	return ('C', a[0]) + ConvertToList(a[1]) + ConvertToList(a[2])

if sys.version_info[0] >= 3:
	def cmp(a, b):
		"""analogue of python 2 cmp function"""
		if  a == b: return 0
		elif a < b: return -1
		elif a > b: return 1
		else: raise ValueError("Incomparable objects")

def CompareStd(a, b, useChangeOmegaN=True):
	"""Compares a and b when they are in the standard form"""
	# also works when a and b are in the standard form for the nth notation system
	# if a and b are in the standard form for the nth notation system, useChangeOmegaN=False can be used for some speed up.
	# Note that because we use Cn rather than C, simple lexicographical comparison would not work.
	def decompose(arg):
		List = []
		while isinstance(arg, tuple):
			List.append([arg[0],arg[1]])
			arg = arg[2]
		List.append([1, arg])
		return list(reversed(List))
		
	if useChangeOmegaN:
		n = max(MaxOmegaUsed(a), MaxOmegaUsed(b))
		a = ChangeOmegaN(a, n)
		b = ChangeOmegaN(b, n)
	if a == b:
		return 0
	if a == 0:
		return -1
	if b == 0:
		return 1
	if isinstance(a, str) and isinstance(b, str):
		return cmp(len(a), len(b))
	a_list = decompose(a)
	b_list = decompose(b)
	# we now compare a_list and b_list lexicographically with the help of CompareStd
	for i in range(min(len(a_list), len(b_list))):
		if a_list[i] != b_list[i]:
			if a_list[i][1] == b_list[i][1]:
				return cmp(a_list[i][0], b_list[i][0])
			return CompareStd(a_list[i][1], b_list[i][1], False)
	return cmp(len(a_list), len(b_list))

def IsBuiltFromBelow(a, b, n, d=0):
	"""returns True iff a is n-built from below from <b with counterexamples required to be >=d instead of just a"""
	# for the function to do what we want, a and b should be standard for the n-th ordinal notation system
	if CompareStd(a, b) < 0:
		return True
	if isinstance(a, str):
		return n >= 1 or CompareStd(a, d) == -1
	if CompareStd(a, d) == -1:
		return IsBuiltFromBelow(a[1], b, n, d) and IsBuiltFromBelow(a[2], b, n, d)
	elif n == 0:
		return False
	else:
		return IsBuiltFromBelow(a[1], b, n-1, a) and IsBuiltFromBelow(a[2], b, n-1, a)

def IsStandard(a, n=0):
	"""return True if a is in the standard form; if n > 0 checks for standard form in the nth notation system"""
	# Return False if a has invalid syntax.
	if a == 0:
		return True  # note: perhaps we should disallow floating point 0.0
	if isinstance(a, str):
		return len(a) > 0 and (n == 0 or len(a) == n) and a == 'W'*len(a)
	if not isinstance(a, tuple) or len(a) != 3:
		return False
	if not isinstance(a[0], int) and not isinstance(a[0], type_long) or a[0] < 1:
		return False
	if not IsStandard(a[1], n) or not IsStandard(a[2], n):
		return False
	if isinstance(a[1], str) and a[1] != 'W' and a[2] == 0:
		return False
	if isinstance(a[2], tuple) and CompareStd(a[1], a[2][1]) >= 0:
		return False
	if n == 0:
		if isinstance(a[2], str) and CompareStd(a[1], 'W'*(len(a[2])+1)) > 0:
			return False
		m = max(MaxOmegaUsed(a), 1)
		a = ChangeOmegaN(a, m)
		return IsBuiltFromBelow(a[1], a, m)
	else:
		return IsBuiltFromBelow(a[1], a, n)

def StandardForm(a, cache=None):
	"""Convert a to the standard form"""
	# We assume that a is a valid term (use CheckSyntax to check that).
	# To speed up computation when we call the function multiple times, we keep a cache of the results.

	def CacheAndReturn(value):
		cache[a_old] = value
		return value

	def MaximizeA(a, b, n, i=0, d=0, ConvertToStandard=True):
		"""Assuming that a and b are in nth standard form, returns the least ordinal a1>=a such that a1 is n-built from below from <b
			i and d and ConvertToStandard are for internal recursion"""
		# We perform an in-order right to left traversal of the term tree of a to find the first counterexample (if any) to a being n-built from below from <b.
		# The counterexample is of the form f = C2(g, h) where f < W_n and g is too large (that is g>=d).  We replace f with W_n and delete everything to the left of f.
		# d and i are used to track the state of our search:
		# d -- maximum ordinal encountered along the path to the current term
		# i -- the number of times we had to increase d along the current path
		#
		# Including conversion to the nth standard form at the end is necessary; an example is a=CCW0CCW00 and b=C0CCW00 (prenex form, W stands for W_2).
		if a == 0 or isinstance(a, str) or CompareStd(a, b) < 0:
			return a
		if ConvertToStandard:
			return ChangeOmegaN(StandardForm(MaximizeA(a, b, n, i, d, False), cache), n)
		if d == 0:
			d = a
			i+=1
		a2_new = MaximizeA(a[2], b, n, i, d, False)
		if a2_new != a[2]:
			return a2_new
		if CompareStd(a[1], d) == -1:
			a1_new = MaximizeA(a[1], b, n, i, d, False)
			if a1_new != a[1]:
				return (1, a1_new, a[2])
			else:
				return a
		else:
			if i==n:
				return 'W'*n
			a1_new = MaximizeA(a[1], b, n, i+1, a[1], False)
			if a1_new != a[1]:
				return (1, a1_new, a[2])
			else:
				return a

	def LargeSafeI(a, a1, b):
		"""Assuming that a and b are in nth standard form, find a large value of i such that a1=MaximizeA(a, C2(a,b), n) equals MaximizeA(a, (i-1, a, C2(a,b))); may return 0 if i can be arbitrarily large"""
		# The function is implemented by recursion on subterms of a.
		if isinstance(b, str) or isinstance(a, str) or a==0:
			return 0
		if a[1] == a1 and a[2] == b:
			return a[0]
		if isinstance(b, tuple) and a[1] == a1 == b[1] and a[2] == b[2]:
			return max(0, a[0]-b[0])
		i1 = LargeSafeI(a[1], a1, b)
		i2 = LargeSafeI(a[2], a1, b)
		if i1*i2 == 0:
			return max(i1, i2)
		else:
			return min(i1, i2)

	if cache is None:
		cache = {}
	if a in cache:
		return cache[a]
	a_old = a
	if not CheckSyntax(a):
		raise ValueError("Invalid ordinal representation syntax")
	if IsStandard(a): # this also takes care of the case a == 0 or a is a string
		return CacheAndReturn(a)
	if isinstance(a, int) or isinstance(a, type_long):
		return CacheAndReturn((a, 0, 0))
	if a[0] == 0:
		return CacheAndReturn(StandardForm(a[2], cache))
	a = (a[0], StandardForm(a[1], cache), StandardForm(a[2], cache))
	n = MaxOmegaUsed(a)
	a = ChangeOmegaN(a, n) # change to the nth notation system to simplify logic
	while isinstance(a[2], tuple) and CompareStd(a[1], a[2][1], False) > 0:
		a = (a[0], a[1], a[2][2])
	if isinstance(a[2], tuple) and a[1] == a[2][1]:
		a = (a[0] + a[2][0], a[1], a[2][2])
	if IsStandard(a, n):
		return CacheAndReturn(ChangeOmegaN(a, 0))
	# The nth standard form of (1, a[1], a[2]) is (1, a1, a[2]) where a1 = MaximizeA(a[1], (1, a[1], a[2]), n)
	# While we can apply this iteratively to convert a to the standard form, a[0] can be large, so
	# we have to work in slices for which a1 is the same.  The key observation is that
	# a1 can only change when the iteration leads to a subterm of a, which is implemented using LargeSafeI.
	while a[0] > 0:
		a1 = MaximizeA(a[1], a, n)
		i = LargeSafeI(a[1], a1, a[2])
		if i == 0 or i >= a[0]:
			i = a[0]
		a2 = (i, a1, a[2])
		if isinstance(a2[2], tuple) and a2[1] == a2[2][1]:
			a2 = (a2[0] + a2[2][0], a2[1], a2[2][2])
		a = (a[0]-i, a[1], a2)
		if a[1] == a[2][1]:
			a = (a[0] + a[2][0], a[1], a[2][2])
			return CacheAndReturn(ChangeOmegaN(a, 0))
	return CacheAndReturn(ChangeOmegaN(a[2],0))

# Note:
# The code above defines the ordinal representation system.
# The code below creates class Ordinal to represent ordinals, and implements ordinal arithmetic.

class Ordinal(object):
	"""Implements ordinal arithmetic."""
	# Note:  Ordinals are essentially treated as immutable objects.

	def __init__(self, Input, **keys):
		# Input can be ordinal, a tuple, a string (only for the W constants), or integer.
        # If check=False is used (as a keyword argument), then skip syntax check and conversion to standard form (to save compute); this assumes
		# that the Input is in the standard form.

		if isinstance(Input, Ordinal):
			self.data = Input.data
			return
		check = keys.get("check", True)
		if check == "strict":  # check="strict" is useful when an operation should always return the standard form, but we want to verify it just in case there is a bug
			if not IsStandard(Input):
				raise ValueError("Nonstandard form ("+str(Input)+")")
			self.data = Input
			return
		if isinstance(Input, int) or isinstance(Input, type_long):
			if Input < 0:
				raise ValueError("Ordinals cannot be negative")
			self.data = StandardForm(Input)
			return
		if check:
			if not CheckSyntax(Input):
				raise ValueError("Invalid syntax for ordinal representation")
			Input = StandardForm(Input)
		self.data = Input

	def __hash__(self):
		return hash(self.data)
	
	# if x is in Ordinal.symbols and x==w**x, then by default prettyprint(self) will use Ordinal.symbols[x] to represent x when x is a subterm of self; useC2, usephi, and usewCK prettyprint options may affect which ordinals are treated as subterms of self.
	symbols = {} 	

	autoprettyprint = True # affects behavior of __repr__

	# prettyprintargs contains default arguments for prettyprint.  This is useful for controlling how ordinals appear using str and repr.
	# For example, you can disable use of phi by executing: Ordinal.prettyprintargs['usephi'] = False
	# Use of phi shortens representations in part by avoiding having to specify the next admissible ordinal from scratch; however, use of phi disrupts quasi-lexicographical comparison.
	# wCK is not used by default because it does not add much and because it has poor integration with one-variable C.
	prettyprintargs = {"poweroperator": "**", "useextendedCNF": True, "usephi": True, "usewCK": False, "useC2": False, "Csymbol": "C", "wsymbol": "w", "Wsymbol": "W", "phisymbol": "phi", "wCKsymbol": "wCK", "symbols":"default", "context": None}

	def __str__(self):
		return self.prettyprint()

	def __repr__(self):
		"""if self.autoprettyprint is True (which is the default), then repr uses pretty printing, which is helpful for interactive use.
If self.autoprettyprint is False, then __repr__  is based on repr(self.data).
To prevent repr from using pretty print by default, set Ordinal.autoprettyprint to False."""
		if self.autoprettyprint:
			if self.isinteger():
				return "Ordinal("+self.prettyprint()+")"
			return self.prettyprint()
		return 'Ordinal('+repr(self.data)+')'

	def __cmp__(self, other):
		if not isinstance(other, Ordinal):
			other = Ordinal(other)
		return CompareStd(self.data, other.data)

	def __eq__(self, other):
		try:
			return self.data == Ordinal(other).data  # (this is faster than using cmp)
		except ValueError:
			return False

	if sys.version_info[0] >= 3: # python 3 does not use __cmp__ special method, so we define the comparison operators manually
		def __lt__(a, b): return a.__cmp__(b) <  0
		def __le__(a, b): return a.__cmp__(b) <= 0
		def __ge__(a, b): return a.__cmp__(b) >= 0
		def __gt__(a, b): return a.__cmp__(b) >  0

	def __nonzero__(self):
		return self.data != 0
	__bool__ = __nonzero__ # used in python 3

	def isinteger(self):
		"""return True iff the ordinal is an integer"""
		if isinstance(self.data, str):
			return False
		return self.data == 0 or self.data[1] == self.data[2] == 0

	def __int__(self):
		if not self.isinteger():
			raise ValueError("Not an integer")
		elif self.data == 0:
			return 0
		else:
			return self.data[0]

	def isWn(self):
		"""return n if self is W(n) (n>0), else return False."""
		if isinstance(self.data, str):
			return len(self.data)
		else:
			return False

	# For convenience, if self.isWn() is True, then arg0, arg1, arg2, args, and C2args will behave as if self must be represented in terms of other ordinals.
	# For example, W(1).args() == (1, W(2), 0).

	def arg0(self):
		if self.data == 0:
			raise ValueError("Not a C-term")
		if self.isWn():
			return 1
		return self.data[0]

	def arg1(self):
		if self.data == 0:
			raise ValueError("Not a C-term")
		if self.isWn():
			return Ordinal('W'*(len(self.data)+1)) # equals W(self.isWn()+1)
		return Ordinal(self.data[1], check=False)

	def arg2(self):
		if self.data == 0:
			raise ValueError("Not a C-term")
		if self.isWn():
			return Ordinal(0)
		return Ordinal(self.data[2], check=False)

	def args(self):
		if self.data == 0:
			raise ValueError("Not a C-term")
		return (self.arg0(), self.arg1(), self.arg2())

	def C2args(self):
		if self == 0:
			raise ValueError("Not a C-term")
		if self.arg0() == 1:
			return self.arg1(), self.arg2()
		return self.arg1(), Cn(self.arg0()-1, self.arg1(), self.arg2(), check=False)

	def C2(self, other, **args):
		check = args.get("check", True)
		return Ordinal((1, self.data, Ordinal(other).data),check=check)

	def C(self, **args):
		base = args.get("base")
		if base:
			return C(Ordinal(base).Cinv()+self)
		result = Ordinal(0)
		if self.isWn() and self.isWn() > 1:
			return W(self.isWn()-1)
		decomposition = self.decompose2()
		for term,count in decomposition:
			if term.isWn():
				result = Cn(count, term, result)
			elif not IsStandard((1, term.data, result.data)):
				return C2(term, result)
			else:
				result = Cn(count, term, result, check=False)
		return result

	def Cinv(self, **args):
		base = args.get("base")
		if base:
			base = Ordinal(base)
			if self < base:
				raise ValueError("self must be >=base")
			elif self == base:
				return base # this is just for efficiency
			return self.Cinv().leftsubtract(base.Cinv())
		termlist = []
		while self:
			termlist.insert(0, (self.arg1(), self.arg0()))
			self = self.arg2()
		return OrdinalSum(w**term[0]*term[1] for term in termlist)

	def base_omega_fixpoint(self):
		"""return the largest fixpoint of x->omega^x that is not above self; return Ordinal(0) if self < epsilon_0"""
		answer = Ordinal(self) # Note:  Here, as elsewhere, it is important to return a copy of self instead of just self.
		## The commented code is a correct, but for efficiency (specifically, avoiding repeated calls to MaxOmegaUsed) we use a lower level implementation.
		#while answer != 0 and answer.arg1() < answer:
		#	answer = answer.arg2()
		#return answer
		data = ChangeOmegaN(answer.data, MaxOmegaUsed(answer.data))
		while isinstance(data, tuple) and CompareStd(data[1], data, False) < 0:
			data = data[2]
		answer.data = ChangeOmegaN(data, 0)
		return answer

	def exp_omega(self):
		"""return omega^x"""
		fixpoint = self.base_omega_fixpoint()
		if fixpoint == self and fixpoint:
			return fixpoint
		else:
			return C2(self, fixpoint, check=False)

	def decompose1(self, expand=False):
		"""return the standard additive decomposition of the ordinal
		if expand=False (default), uses [a, n] (even if n=1) in place of [a, a, ..., a]"""
		# Note:  expand may result in exponential increase of size, and so is not used in the implementation of Ordinal, and similarly for decompose2.
		if expand: 
			decomposition = []
			for ordinal, n in self.decompose1():
				for i in range(n): # (we use a loop here to ensure that each element is a separate copy of ordinal)
					decomposition.append(Ordinal(ordinal))
			return decomposition
		return [[x[0].exp_omega(), x[1]] for x in self.decompose2()]

	def decompose2(self, expand=False):
		"""if expand=True, return [x1, x2, ...] where self = w**x1+w**x2+... and x1 >= x2 >= ...
		if expand=False (default), use [a, n] (even when n=1) in place of [a, a, ..., a]"""
		# An interesting note is that ordinary ordinal arithmetic can be implemented
		# just using this function, the inverse, and comparison for fixpoints of exponentiation base omega.
		if expand:
			decomposition = []
			for ordinal, n in self.decompose2():
				for i in range(n):  # (we use a loop here to ensure that each element is a separate copy of ordinal)
					decomposition.append(Ordinal(ordinal))
			return decomposition
		if self == 0:
			return []
		fixpoint = self.base_omega_fixpoint()
		if fixpoint == self:
			return [[fixpoint, 1]]
		decomposition = []
		arg = self
		while arg != fixpoint:
			decomposition.insert(0, [arg.arg1(), arg.arg0()])
			arg = arg.arg2()
		if decomposition[0][0] == fixpoint and fixpoint:
			decomposition[0][1]+=1
		elif decomposition[0][0] < fixpoint:
			decomposition.insert(0, [fixpoint, 1])
		return decomposition

	def decompose_extended(self, base):
		"""like decompose1, but uses base (and multiplication by ordinals <base) instead of w"""
		base = Ordinal(base)
		if base == C2(1,0): # this is just for efficiency
			return [ [item[0], Ordinal(item[1])] for item in self.decompose1()]
		exponent = base.log(self)
		factor, remainder = divmod(self, base**exponent)
		if remainder:
			return [[base**exponent, factor]] + remainder.decompose_extended(base)
		else:
			return [[base**exponent, factor]]	

	def islimit(self):
		"""return True iff self is a limit ordinal"""
		return self != 0 and self.arg1() > 0

	def ispowerofomega(self):
			"""return True iff self is a power of omega"""
			decomposition = self.decompose2()
			return len(decomposition) == 1 and decomposition[0][1] == 1

	def log_omega(self):
		"""return the largest y such that omega^y <= self"""
		if self == 0:
			raise ValueError("log_omega of 0 is not defined")
		return self.decompose2()[0][0]

	def __add__(self, other):
		return OrdinalSum(self, other)

	def __mul__(self, other):
		other = Ordinal(other)
		if self == 0 or other == 0:
			return Ordinal(0)
		elif other == 1:
			return Ordinal(self)
		elif self == 1:
			return other
		list2 = other.decompose1()
		if len(list2) != 1:
			return OrdinalSum(self*item[0]*item[1] for item in list2)
		if not list2[0][0].isinteger():
			# here, other is an integral multiple of a nonzero power of omega
			# Note that (w^a+c)*w^b == w^(a+b) if b > 0 and c < w^(a+1).
			# and d*e*f == d*(e*f)
			return (self.log_omega() + other.log_omega()).exp_omega()*list2[0][1]
		n = list2[0][1] # n>1 is an integer and we have to compute self*n (list2[0][0]==1)
		list1 = self.decompose1()
		if len(list1) != 1 or list1[0][1] != 1:
			return list1[0][0]*(list1[0][1]*(n-1))+self
		if self == self.base_omega_fixpoint():
			return Cn(n-1, self, self, check=False)
		else: # here self.args() == (1, self.log_omega(), self.base_omega_fixpoint())
			return Cn(n, self.arg1(), self.arg2(), check=False)

	def __pow__(self, other):
		other = Ordinal(other)
		if other == 0 or self == 1:
			return Ordinal(1)
		elif other == 1:
			return Ordinal(self)
		elif self == 0:
			return Ordinal(0)
		elif self.isinteger() and other.isinteger():
			return Ordinal(self.data[0]**other.data[0])
		if not other.isinteger() and not other.islimit():
			return self**other.arg2() * self**other.arg0()
		if other.islimit() or self.ispowerofomega():
			if self.isinteger():
				return (other//C2(1,0)).exp_omega()
			else:
				return (self.log_omega()*other).exp_omega()
		# other is an integer here
		return OrdinalProduct(self for n in range(int(other)))

	def __radd__(self, other):  return Ordinal(other)+self
	def __rmul__(self, other):  return Ordinal(other)*self
	def __rpow__(self, other):  return Ordinal(other)**self

	def leftsubtract(self, other):
		"""return x such that other+x == self"""
		other = Ordinal(other)
		if self < other:
			raise ValueError("ordinal values cannot be negative")
		list1 = self.decompose1()
		list2 = other.decompose1()
		cutoff = 0
		while cutoff < min(len(list1), len(list2)) and list1[cutoff] == list2[cutoff]:
			cutoff+=1
		if cutoff < min(len(list1), len(list2)) and list1[cutoff][0] == list2[cutoff][0]:
			list1[cutoff][1]-=list2[cutoff][1]
		return OrdinalSum(item[0]*item[1] for item in list1[cutoff:])

	def rightsubtract(self, other):
		"""return the least x such that x+other == self; raise ValueError if such x does not exist (for example w.rightsubtract(1) does not exist)"""
		other = Ordinal(other)
		if self < other:
			raise ValueError("ordinal values cannot be negative")
		if self == other:
			return Ordinal(0)
		if other == 0:
			return Ordinal(self)
		list1 = self.decompose1()
		list2 = other.decompose1()
		if len(list1) < len(list2):
			raise ValueError("result does not exist")
		for i in range(len(list2)-1):
			if list1[-1-i] != list2[-1-i]:
				raise ValueError("result does not exist")
		item1 = list1[-len(list2)]
		item2 = list2[0]
		if item1[0] != item2[0] or item1[1] < item2[1]:
			raise ValueError("result does not exist")
		return OrdinalSum(item[1]*item[0] for item in list1[:-len(list2)]) + item1[0]*(item1[1]-item2[1])

	def __floordiv__(self, other):
		"""return the maximum x such that other*x <= self"""
		other = Ordinal(other)
		if other == 0:
			raise ZeroDivisionError("ordinal division by 0")
		if self < other:
			return Ordinal(0)
		if self.isinteger():
			return Ordinal(self.data[0]//other.data[0])
		if other.isinteger():
			if self.islimit():
				return self
			return self.arg2() + self.arg0()//other
		# min(self, other) >= w
		if other*C2(1,0) > self:
			guess = self.decompose1()[0][1]//other.decompose1()[0][1]
			if other*guess <= self:
				return Ordinal(guess)
			else:
				return Ordinal(guess).leftsubtract(1)
		base_quotient = self.log_omega().leftsubtract(other.log_omega()).exp_omega()*self.decompose1()[0][1]
		return base_quotient + self.leftsubtract(other*base_quotient)//other # recursive computation of quotient

	def __divmod__(self, other):
		"""return a, b such that self=other*a+b and b<other.
This corresponds to left division: x == y*(x//y) + x%y == y*x//y; because of lack of commutativity, x need not equal x*y//y."""
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
		if base == C2(1,0):
			return arg.log_omega() # this is just for efficiency
		decomposition = arg.decompose1()
		if base.isinteger():
			result = 0
			while base**result <= decomposition[0][1]:
				result+=1   # this is not very efficient, but it is still polynomial time
			return C2(1,0)*decomposition[0][0].log_omega() + (result - 1)
		approximate_log = arg.log_omega() // base.log_omega()
		if base**approximate_log > arg: # this will only happen if base is not a power of omega
			return approximate_log.arg2() # Note: Here, approximate_log == approximate_log.arg2()+1.
		else:
			return approximate_log

	def cnf_changebase(self, base1, base2):
		"""change base in Cantor Normal Form for self. For example (w**2+3).cnf_changebase(w, W_1) == W(1)**2+3
		raise ValueError if the new base is too small"""
		base1 = Ordinal(base1)
		base2 = Ordinal(base2)
		if base1 < self.base_omega_fixpoint():
			raise ValueError("Old base is too small")
		if self == base1:
			return base2
		if self < min(base1, base2):
			return self
		decomposition = self.decompose_extended(base1)
		for ordinal, factor in decomposition:
			if factor >= base2:
				raise ValueError("New base is too small")
		return OrdinalSum(base2**(base1.log(item[0]).cnf_changebase(base1, base2))*item[1] for item in decomposition)

	# Note:  While the functions above depend only on the general properties of C,
	# implementation of functions below partly depends on the exact definition of the standard form.

	def NextNCorrect(self, n):
		"""return the least ordinal above self that can be collapsed onto self at least n times; NextNCorrect(Ordinal(0), n) == W(n)"""
		n = int(n)
		if n < 1:
			raise ValueError("n must be at least 1")
		m = MaxOmegaUsed(self.data)
		result = 'W'*max(m+1,n)
		if m+1 > n:
			for i in range(m+1-n):
				result = (1, result, self.data)
		return Ordinal(result) # note: result need not be in the standard form since conversion to standard form is automatic

	def NextAdmissible(self):
		"""Return the least admissible ordinal (>omega) above self"""
		return self.NextNCorrect(1)



	def C2criticalsequence(self, cache=None):
		"""Return ascending sequence S of ordinals such that x in S iff forall y<x self.C2(y).arg1() > self.C2(x).arg1()."""
		# cache is used for various conversions to the standard form.
		# The code assumes (and we conjecture) that all members of the sequence are subterms of self.
		# Notes about S:
		# * S[0] == 0
		# * self is maximal in "C2(self, x)" iff x >= S[-1]
		def Cterms(x):
			# return the list of all terms in the representation of x
			if x == 0 or x.isWn():
				return [x]
			return [x] + Cterms(x.arg1()) + Cterms(x.arg2())
		termlist = Cterms(self)
		if cache is None:
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
			value = StandardForm((1, self.data, item.data), cache)
			if isinstance(value, str):
				value = 'W'*(len(value)+1)
			else:
				value = value[1]
			if value != lastvalue:
				seq.append(item)
			lastvalue = value
			if value == self:
				break # this is just for efficiency
		return seq

	def C2iterate(self, count, base=0, cache=None):
		"""Iterate x -> C2(self, x) count number of times, starting at x=base, and return the resulting ordinal. count can be any ordinal."""
		# cache is used to store results of conversions to the StandardForm
		count = Ordinal(count)
		base = Ordinal(base)
		if not count:
			return base
		if count.isinteger():
			return Cn(count, self, base)
		if self.base_omega_fixpoint() <= base:
			return base + self.exp_omega()*count
		if cache is None:
			cache = {}
		if len(count.decompose1()) > 1:
			result = base
			for cnt, n in count.decompose1():
				result = self.C2iterate(cnt*n, result, cache)
			return result
		count, n = count.decompose1()[0]
		# There are two possibilities: C2iterate(self, count, base) == count.base_omega_fixpoint() == count, or C2iterate(self, count, base) > count.base_omega_fixpoint(), and we have to determine which.
		seq = self.C2criticalsequence(cache)
		if count > base:
			crit_term = max(item for item in seq if item < count)
			self_max = C2(self, crit_term).arg1() # self_max is maximized self in "C2(self, x)" for x that are just below count
			if count.arg1() > self_max + count: # this is necessary and sufficient for C2iterate(self, count, base) == count
				return self.C2iterate(count*(n-1), count, cache) # this will be reached at most once
			# at this point, C2iterate(self, count, base) > count.base_omega_fixpoint()
			base = max(base, count.base_omega_fixpoint())
		# We now use seq to correctly define the iteration.
		# A key observation is that above base, the critical sequence of self agrees with that of self+count.log_omega(), so
		# we can then compute the iteration for each interval in the critical sequence.
		while n > 0:
			guess_degree = C2(self, base).arg1() + count.log_omega()
			guess_n = Cn(n, guess_degree, base)
			seq_ = [x for x in seq if x>base]
			if not seq_ or min(seq_) >= guess_n:
				return guess_n
			guess_1 = C2(guess_degree, base)
			crit_term = min(seq_)
			if crit_term < guess_1:
				base = crit_term
				continue
			# here guess_1 <= crit_term < guess_n
			# furthermore, crit_term is Cn(m, guess_1.arg1(), guess_1.arg2()) for some m
			base = crit_term
			n = n - crit_term.arg0() + guess_1.arg0() - 1
		# This point should never be reached.

	def Citerate(self, count, base=0, cache=None):
		"""Iterate x -> C(self, base=x) count number of times, starting at x=base, and return the resulting ordinal. count can be any ordinal."""
		# cache is used to store results of conversions to the StandardForm
		count = Ordinal(count)
		base = Ordinal(base)
		if self == 0 or count == 0:
			return base
		if count == 1:
			return C(self, base=base)
		if cache is None:
			cache = {}
		decomposition = self.decompose2()
		mainterm, maintermcount = decomposition[0]
		if not count.isinteger():
			count2 = count%w
			count1 = count.rightsubtract(count2)
			return self.Citerate(count2, mainterm.C2iterate(count1, base, cache), cache)
		count = int(count)
		# Note:  At this point, a simple but exponentially slow implementation would be to return C(self, base=self.Citerate(count-1, base)).
		crit_term = mainterm.C2criticalsequence(cache)[-1]
		if crit_term > base:
			if crit_term >= Cn(count, mainterm, base):
				return Cn(count, mainterm, base)
			# do binary search to find the least y such that Cn(y, mainterm, base) >= crit_term
			min_n = 0
			max_n = count
			while min_n + 1 < max_n:
				midpoint = (min_n + max_n)//2
				value = Cn(midpoint, mainterm, base)
				if value < crit_term:
					min_n = midpoint
				elif value > crit_term:
					max_n = midpoint
				else:
					min_n = max_n = midpoint
					break
			base = Cn(max_n, mainterm, base)
			count -= max_n
		# here crit_term <= base
		if len(decomposition) == 1:
			return Cn(count*maintermcount, mainterm, base)
		secondterm = decomposition[1][0]
		if Cinv(C(self, base=base), base=base) < w**mainterm*(maintermcount+1):
			return C(self.leftsubtract(w**mainterm*maintermcount), base=Cn(count*maintermcount, mainterm, base))
		# do binary search to find the largest y <= (count-1)*(maintermcount+1) such that Cn(y, secondterm, base) == Cn(y, mainterm, base)
		min_n = 0
		max_n = (count-1)*(maintermcount+1)+1
		while min_n + 1 < max_n:
			midpoint = (min_n + max_n)//2
			value = Cn(midpoint, mainterm, base)
			if Cn(midpoint, secondterm, base) == Cn(midpoint, mainterm, base):
				min_n = midpoint
			else:
				max_n = midpoint
		count_decrement = min_n//(maintermcount+1)
		base = Cn(count_decrement*(maintermcount+1), mainterm, base)
		count -= count_decrement
		return C(self.leftsubtract(w**mainterm*maintermcount), base=Cn(count*maintermcount, mainterm, base))

	def phi(self, other):
		"""a.phi is the ath fixpoint function (with Ordinal(0).phi being exponentiation base w), and a.phi(b) is point b in the range of a.phi."""
		return phi_n(self, other)

	def phi_inv(base, arg):
		"""return the maximum x such that base.phi(x) <= arg; raise exception if arg < base.phi(0)"""
		arg = Ordinal(arg)
		if base == 0:
			return arg.log_omega()
		if arg < base:
			raise ValueError("Value too small for self.phi_inv(value) to be defined.")
		# here 0 < base <= arg
		A = arg.NextAdmissible() # next "admissible" ordinal above arg
		while arg and arg.arg1() < A*base:
			arg = arg.arg2()
		last_arg1 = None
		values = [] # the use of the values variable (as opposed to doing the summation incrementally) is for efficiency
		while arg and arg.arg1() < A*(base+1):
			value = (arg.arg1() % A).exp_omega()*arg.arg0()
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
		if self.arg1() < self:
			return Ordinal(0), self.arg1()
		A = self.NextAdmissible()
		a = self.arg1()//A
		if a >= A: # this is necessary and sufficient for self to be unreachable from below using phi
			return Ordinal(self), Ordinal(0)
		else:
			return a, a.phi_inv(self)

	def prettyprint(self, **args):
		"""Print ordinal in a human-readable form.
Behavior is configurable with keyword arguments and with Ordinal.prettyprintargs.  For example, use poweroperator='^' to use '^' for power instead of the default '**'.  If x is in symbols (symbols defaults to Ordinal.symbols) and x==w**x, then x will be represented by symbols[x]."""
		def getarg(arg):
			return args.get(arg, Ordinal.prettyprintargs[arg])
		# Configurable parameters
		poweroperator = getarg("poweroperator") # symbol for the power operator
		useextendedCNF = getarg("useextendedCNF") # when appropriate, use Cantor normal form on bases >w.
		usephi = getarg("usephi") # use the Veblen fixpoint functions
		usewCK = getarg("usewCK") # use wCK function
		useC2 = getarg("useC2") # use C2 and Cn in place of C
		wsymbol = getarg("wsymbol")
		Wsymbol = getarg("Wsymbol")
		Csymbol = getarg("Csymbol")
		phisymbol = getarg("phisymbol")
		wCKsymbol = getarg("wCKsymbol")
		symbols = getarg("symbols") # symbols to use to represent certain ordinals; see Ordinal.symbols comment
		if symbols == "default":
			symbols = Ordinal.symbols
		if symbols is None:
			symbols = {}
		context = getarg("context") # the context in which the ordinal is used ('mul' -- '*', 'pow1' -- first argument of '**', 'pow2' -- second argument of '**'); this argument is used to automatically add external parentheses if necessary.
		if self.isinteger():
			return str(int(self))
		elif self.isWn():
			if self in symbols:
				return symbols[self]
			return Wsymbol + '('+str(self.isWn())+')'
		elif self == C2(1,0):
			return wsymbol
		if self.base_omega_fixpoint() == self:
			if self in symbols:
				return symbols[self]
			args["context"] = None
			if usephi:
				a, b = self.phi_args()
				if a < self:
					return phisymbol+'('+a.prettyprint(**args)+','+b.prettyprint(**args)+')'
			if usewCK:
				a = wCK_inv(self)
				if a < self and wCK(a) == self:
					return wCKsymbol+'(' + a.prettyprint(**args) + ')'
			if not useC2:
				return Csymbol+'('+self.Cinv().prettyprint(**args) + ')'
			if self.arg0() == 1:
				return 'C2(' + self.arg1().prettyprint(**args) + ',' + self.arg2().prettyprint(**args) + ')'
			else:
				return 'Cn(' + str(self.arg0()) + ',' + self.arg1().prettyprint(**args) + ',' + self.arg2().prettyprint(**args) + ')'
		# Here the topmost operation is addition, multiplication, or power.
		if useextendedCNF:  # combine terms as appropriate for the extended CNF.
			base = max(C2(1,0), self.base_omega_fixpoint())
		else:
			base = C2(1,0)
		args2 = {}
		for item in args:
			args2[item] = args[item]
		if base == C2(1,0) and len(self.decompose1()) > 1: # this is just for efficiency
			args2['context'] = None
			values = [(item[0]*item[1]).prettyprint(**args2) for item in self.decompose1()]
			value = values[0]
			for item in values[1:]:
				value += '+' + item
			if context in ('mul', 'pow1', 'pow2'):
				value = '(' + value + ')'
			return value
		exponent = base.log(self)
		factor, remainder = divmod(self, base**exponent)
		if remainder != 0:
			args2['context'] = None
			remainder_print = remainder.prettyprint(**args2)
			main_print = (base**exponent*factor).prettyprint(**args2)
			value = main_print + '+' + remainder_print
			if context in ('mul', 'pow1', 'pow2'):
				value = '(' + value + ')'
			return value
		if factor != 1:
			args2['context'] = 'mul'
			factor_print = factor.prettyprint(**args2)
			main_print = (base**exponent).prettyprint(**args2)
			value = main_print + '*' + factor_print
			if context in ('pow1', 'pow2'):
				value = '(' + value + ')'
			return value
		# note:  Here exponent != 1 and exponent != self
		args2['context'] = 'pow1'
		base_print = base.prettyprint(**args2)
		args2['context'] = 'pow2'
		exponent_print = exponent.prettyprint(**args2)
		value = base_print + poweroperator + exponent_print
		if context == 'pow1': # not necessary since this condition will never be triggered
			value = '(' + value + ')'
		return value



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
	i = 0
	while i < len(decomposition)-1:
		if decomposition[i+1][0] < decomposition[i][0]:
			i+=1
		elif decomposition[i+1][0] == decomposition[i][0]:
			decomposition[i][1]+=decomposition[i+1][1]
			del decomposition[i+1]
		else:
			del decomposition[i]
			i = max(i-1, 0)
	if not decomposition:
		return Ordinal(0)
	fixpoint = decomposition[0][0].base_omega_fixpoint()
	if fixpoint != 0 and decomposition[0][0] == fixpoint:
		decomposition[0][1]-=1
		if decomposition[0][1] == 0:
			del decomposition[0]
	result = fixpoint.data
	for a, n in decomposition:
		result = (n, a.data, result)
	return Ordinal(result, check=False)

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
		decomposition+=Ordinal(arg).decompose1()
	decomposition.sort(reverse=True) # this line is what makes the sum symmetric
	return OrdinalSum(item[0]*item[1] for item in decomposition)

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
	if len(arg2.decompose1()) != 1:
		return SymmetricOrdinalSum(SymmetricOrdinalProduct(arg1, arg[0]*arg[1]) for arg in arg2.decompose1())
	if len(arg1.decompose1()) != 1:
		return SymmetricOrdinalSum(SymmetricOrdinalProduct(arg[0]*arg[1], arg2) for arg in arg1.decompose1())
	return SymmetricOrdinalSum(arg1.log_omega(), arg2.log_omega()).exp_omega() * (arg1.decompose1()[0][1]*arg2.decompose1()[0][1])

def phi_n(*args):
	"""n-variable Veblen fixpoint function: phi_n(c) = w^c; phi_n(b, c) = phi(b, c), phi(1, 0, c) = Gamma_{c}, and so on"""
	# this function is used to implement Ordinal.phi
	if len(args) == 0:
		raise ValueError("phi_n requires at least one argument")
	args = [Ordinal(arg) for arg in args]
	if OrdinalSum(args[:-1]) == 0:
		return args[-1].exp_omega()
	A = max(args).NextAdmissible()
	A_pred = max(args) # the predecessor admissible ordinal of A
	while A_pred and A_pred.arg1() < A.NextNCorrect(2):
		A_pred = A_pred.arg2()
	# note that A_pred <= max(args) < A
	degree = OrdinalSum(A**(len(args)-1-n)*args[n] for n in range(len(args)-1))
	base = max(A_pred, degree.C2criticalsequence()[-1])
	if max(args[:-1]) < base:
		count = args[-1].leftsubtract(base)
	elif max(args[:-1]) == base:
		count = args[-1]
	else:
		count = 1+args[-1]
	return degree.C2iterate(count, base)

def phi_extended(self, Omega, arg):
	"""extension of Veblen functions using an argument structure based on Cantor Normal Form of self base Omega;
	for example, the large Veblen ordinal equals phi_extended(W_1**W_1, W_1, 0) (== phi_extended(w**w, w, 0)) and the small Veblen ordinal equals phi_extended(W_1**w, W_1, 0)"""
	# phi_extended is a generalization of phi_n and the implementation is similar to (and based on) the implementation of phi_n
	# Using just 0, addition, and phi_extended, one can reach any ordinal below the Bachmann-Howard ordinal.
	def get_arglist(self):
		# get a list of ordinals that are used in the Cantor Normal Form (base Omega) of self
		if self < Omega:
			return [self]
		List = []
		decomposition = self.decompose_extended(Omega)
		for ordinal, factor in decomposition:
			List += get_arglist(Omega.log(ordinal)) + [factor]
		return List

	self = Ordinal(self)
	Omega = Ordinal(Omega)
	arg = Ordinal(arg)
	if self >= C2(Omega.NextAdmissible(), Omega):
		raise ValueError("phi_extended is not defined/implemented for notations beyond Cantor Normal Form")
	if self == 0:
		return arg.exp_omega()
	args = get_arglist(self)
	A = max(args+[arg]).NextAdmissible()
	A_pred = max(args+[arg]) # the predecessor admissible ordinal of A
	while A_pred and A_pred.arg1() < A.NextNCorrect(2):
		A_pred = A_pred.arg2()
	# note that A_pred <= max(args+[arg]) < A
	degree = A*self.cnf_changebase(Omega, A)
	base = max(A_pred, degree.C2criticalsequence()[-1])
	if max(args) < base:
		count = arg.leftsubtract(base)
	elif max(args) == base:
		count = arg
	else:
		count = 1+arg
	return degree.C2iterate(count, base)

def W(n):
	"""the least ordinal that can be collapsed n times; see the notation system for explanation"""
	n = int(n)
	if n == 0:
		raise ValueError("W(0) is undefined")
	return Ordinal('W'*n)

def wCK(a):
	"""return omega_a^{CK}; CK stands for Church-Kleene"""
	a = Ordinal(a)
	if a == 0:
		return w
	return a.NextNCorrect(2).C2iterate(a)

def wCK_inv(a):
	"""return the largest ordinal b such that wCK(b) <= a; raise ValueError if a<w"""
	if a < w:
		raise ValueError("ordinal is too small")
	elif a < W(1):
		return Ordinal(0)
	W2next = a.NextNCorrect(2)
	while a.arg1() < W2next:
		a = a.arg2()
	result = Ordinal(0)
	while a and a.arg1() < W2next+a:
		result = w**a.arg1().leftsubtract(W2next)*a.arg0() + result
		a = a.arg2()
	result = a + result
	return result

def C(a, **args):
	"""Return the (notation specific) collapse of a; or collapse of a above base if base keyword argument is supplied, C(a, base=b) = C(Cinv(b)+a). C (without base) is continuous, monotonic, and onto.  C is the one variable analog of C2: C2(a_1,C2(a_2,... C2(a_n,base)..)) (if each a_i is maximal) = C(w**a_n+...w**a_2+w**a_1,base=base)."""
	base = args.get("base")
	return Ordinal(a).C(base=base)

def Cinv(a, **args):
	"""return the largest ordinal b such that a = C(b); like C, accepts base keyword argument"""
	base = args.get("base")
	return Ordinal(a).Cinv(base=base)

def C2(a, b, **args):
	"""C2(a, b) == C(w**a, base=b); see the notation system for details"""
	check = args.get("check", True) # if check=False, assume that (1,a.data,b.data) is standard form
	return Ordinal(a).C2(b, check=check)

def Cn(n, a, b, **args):
	"""finite iteration of C2 (for example, Cn(2, a, b) == C2(a, C2(a, b))); n is the number of iterations"""
	check = args.get("check", True) # if check=False, assume that (n,a.data,b.data) is standard form
	n = int(n)
	return Ordinal((n, Ordinal(a).data, Ordinal(b).data), check=check)

def phi(a, b):
	"""Veblen fixpoint function"""
	return Ordinal(a).phi(b)

# useful ordinals
w = C2(1,0)
W_1 = W(1)  # Church-Kleene ordinal
W_2 = W(2)
W_3 = W(3)
epsilon_0 = C(W_1)
Gamma_0 = C(W_1**W_1)

if __name__ == "__main__" and len(sys.argv) >= 2 and sys.argv[1] in ['-h', '-help', '--help']:
	print(__doc__)
