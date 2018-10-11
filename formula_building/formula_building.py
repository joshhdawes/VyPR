"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""

This module contains logic for constructing formulas in the logic found in my notes.

Each possible atom has its own class, ie:

StateValueInInterval - models the atom (s(x) in I) for some state s, a name x and an interval (list) I.
TransitionDurationInInterval - models the atom (d(delta t) in I) for some transition delta t and an interval (list) I.

"""

from monitor_synthesis import formula_tree
import inspect
# be careful with versions here...
from collections import OrderedDict

class If(object):
	"""
	Upon instantiation, this models an incomplete formula - calling then() returns a complete formula tree.
	This is basically syntactic sugar.
	"""

	def __init__(self, formula):
		self._test = formula

	def then(self, formula):
		return formula_tree.ifthen(self._test, formula)

	def __repr__(self):
		return "Incomplete formula: %s" % self._test


class Forall(object):
	"""
	Models a single instance of forall quantification.
	Defines a method called Forall that can be used multiple times to construct
	a sequence of quantifiers.
	This class should always hold the current quantification structure.
	"""
	def __init__(self, is_first=True, bind_variables=None, **bind_variable):
		"""
		Given a bind variable (bind_variable_name is the variable name,
		and bind_variable_value is either StaticState or StaticTransition),
		check that, if is_first is true, the bind variable is independent.
		"""

		bind_variable_name = bind_variable.keys()[0]
		bind_variable_obj = bind_variable.values()[0]

		self.bind_variables = bind_variables

		"""
		resolve the bind variable on which this one depends
		this consists of using the current bind variable name
		to reference the actual bind variable value in the bind_variables dictionary
		"""
		if not(is_first):
			bind_variable_obj._required_binding = self.bind_variables[bind_variable_obj._required_binding]

		bind_variable_final = bind_variable_obj.complete_instantiation(bind_variable_name)
		if self.bind_variables is None:
			self.bind_variables = OrderedDict({bind_variable_name : bind_variable_final})
		else:
			self.bind_variables.update({bind_variable_name : bind_variable_final})

		self._bind_variables = self.bind_variables.values()

		# defined by calling Formula
		self._formula = None

	def __repr__(self):
		if self._formula is None:
			return "Forall(%s)" % self.bind_variables
		else:
			return "Forall(%s).Formula(%s)" % (self.bind_variables, self.get_formula_instance())

	def Forall(self, **bind_variable):
		# return an instance 
		return Forall(is_first=False, bind_variables=self.bind_variables, **bind_variable)

	def get(self, key):
		return self.bind_variables[key]

	# syntactic sugar
	def Check(self, formula_lambda):
		return self.Formula(formula_lambda)

	def Formula(self, formula_lambda):
		"""
		Store the formula lambda, which itself returns a formula when given
		bind variables, for later use.
		"""
		self._formula = formula_lambda
		# generate instantiated formula to compute its atoms
		self._formula_atoms = formula_tree.get_positive_formula_alphabet(self.get_formula_instance())
		return self

	def get_formula_instance(self):
		"""
		Instantiate the formula using the lambda stored.
		"""
		# use the arguments of the lambda function
		argument_names = inspect.getargspec(self._formula).args
		bind_variables = map(lambda arg_name : self.bind_variables[arg_name], argument_names)
		return self._formula(*bind_variables)

class changes(object):
	"""
	Syntactic sugar for specifications.
	"""

	def __init__(self, name_changed, after=None):
		self._name = None
		self._name_changed = name_changed
		self._required_binding = after

	def complete_instantiation(self, bind_variable_name):
		return StaticState(bind_variable_name, self._name_changed, self._required_binding)

class calls(object):
	"""
	Syntactic sugar for specifications.
	"""

	def __init__(self, operates_on, after=None):
		self._operates_on = operates_on
		self._required_binding = after

	def complete_instantiation(self, bind_variable_name):
		return StaticTransition(bind_variable_name, self._operates_on, self._required_binding)

class StaticState(object):
	"""
	Models a binding obtained from a QD consisting of states.
	Needs to be modified to only allow certain methods (equals, length, etc) to be called
	if the __call__ method has already been called, and throw an exception otherwise.
	"""

	def __init__(self, bind_variable_name, name_changed, uses=None):
		self._bind_variable_name = bind_variable_name
		self._name = None
		self._name_changed = name_changed
		self._required_binding = uses

	def __call__(self, name):
		self._name = name
		return self

	def _in(self, interval):
		return formula_tree.StateValueInInterval(self, self._name, interval)

	def equals(self, value):
		return formula_tree.StateValueEqualTo(self, self._name, value)

	def length(self):
		return formula_tree.StateValueLength(self)

	def next_call(self, function):
		return NextStaticTransition(self, function)

	def _next_transition(self, operates_on):
		return NextStaticTransition(self, operates_on)

	def __repr__(self):
		if self._required_binding:
			return "%s = StaticState(changes=%s, uses=%s)" % (self._bind_variable_name, self._name_changed, self._required_binding)
		else:
			return "%s = StaticState(changes=%s)" % (self._bind_variable_name, self._name_changed)

	def __eq__(self, other):
		return (type(other) is StaticState and
			self._bind_variable_name == other._bind_variable_name and
			self._name == other._name and
			self._name_changed == other._name_changed and
			self._required_binding == other._required_binding)

class StaticStateLength(object):
	"""
	Models the length being measured of a value given by a state from a QD.
	"""

	def __init__(self, static_state):
		self._static_state = static_state

	def _in(self, interval):
		return formula_tree.StateValueLengthInInterval(self, self._static_state._name, interval)


class StaticTransition(object):
	"""
	Models a binding obtained from a QD consisting of transitions.
	"""

	def __init__(self, bind_variable_name, operates_on, uses=None):
		self._bind_variable_name = bind_variable_name
		self._operates_on = operates_on
		self._required_binding = uses

	def duration(self):
		return Duration(self)

	def _next_transition(self, operates_on):
		return NextStaticTransition(self, operates_on)

	def __repr__(self):
		if self._required_binding:
			return "%s = StaticTransition(operates_on=%s, uses=%s)" % (self._bind_variable_name, self._operates_on, self._required_binding)
		else:
			return "%s = StaticTransition(operates_on=%s)" % (self._bind_variable_name, self._operates_on)

	def __eq__(self, other):
		return (type(other) is StaticTransition and
			self._bind_variable_name == other._bind_variable_name and
			self._operates_on == other._operates_on and
			self._required_binding == other._required_binding)

class NextStaticTransition(StaticTransition):
	"""
	Models a next transition obtained from another static object.
	"""

	def __init__(self, static_object, operates_on):
		self._centre = static_object
		self._operates_on = operates_on

	def __repr__(self):
		return "next_transition(%s, %s)" % (str(self._centre), self._operates_on)

	def __eq__(self, other):
		return (type(other) is NextStaticTransition and
			self._centre == other._centre and
			self._operates_on == other._operates_on)


class Duration(object):
	"""
	Models the duration of a transition.
	"""

	def __init__(self, transition):
		self._transition = transition

	def _in(self, interval):
		if type(interval) is list:
			return formula_tree.TransitionDurationInInterval(self._transition, interval)
		elif type(interval) is tuple:
			return formula_tree.TransitionDurationInOpenInterval(self._transition, interval)
		else:
			raise Exception("Duration predicate wasn't defined properly.")

def derive_composition_sequence(atom):
	"""
	Given an atom, derive the sequence of operator compositions.
	"""
	sequence = [atom]
	if type(atom) is formula_tree.TransitionDurationInInterval:
		current_operator = atom._transition
	elif type(atom) is formula_tree.StateValueEqualTo:
		sequence.append(atom._state)
		return sequence
	elif type(atom) is formula_tree.StateValueInInterval:
		sequence.append(atom._state)
		return sequence

	while type(current_operator) is NextStaticTransition:
		sequence.append(current_operator)
		current_operator = current_operator._centre

	# add the input bind variable to the composition sequence
	sequence.append(current_operator)
	return sequence