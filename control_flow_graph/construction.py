"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""

This module contains logic for construction of a specialised control flow graph.

"""

import ast
import os
import sys
import argparse
import traceback
from StringIO import StringIO
import datetime
import time
import threading
import Queue

from graphviz import Digraph
sys.path.append(".")
from monitor_synthesis import formula_tree
from formula_building.formula_building import *

vertices = []

class CFGVertex(object):
	"""
	This class represents a vertex in a control flow graph.
	Vertices correspond to states - a new state is induced when the value to which
	a name is mapped in Python code is changed.
	"""

	def __init__(self, name_changed):
		"""
		Given the name changed in the state this vertex represents,
		store it.
		Vertices can also have multiple edges leading out of them into next states.
		"""
		self._name_changed = name_changed
		self.edges = []
		self._previous_edge = None

	def add_outgoing_edge(self, edge):
		edge._source_state = self
		self.edges.append(edge)

	def __repr__(self):
		#return "%s=> %s" % (self._name_changed, self.edges)
		return "%s %i" % (self._name_changed, id(self._name_changed))

class CFGEdge(object):
	"""
	This class represents an edge in a control flow graph.
	"""

	def __init__(self, condition, instruction=None):
		self._condition = condition
		self._instruction = instruction
		self._source_state = None
		self._target_state = None

		if type(self._instruction) is ast.Assign:
			if type(self._instruction.value) is ast.Call:
				self._operates_on = [self._instruction.targets[0].id, self._instruction.value.func.id]
			else:
				self._operates_on = self._instruction.targets[0].id
		elif type(self._instruction) is ast.Expr and hasattr(self._instruction.value, "func"):
			self._operates_on = self._instruction.value.func.id
		else:
			self._operates_on = self._instruction

	def set_target_state(self, state):
		self._target_state = state
		if not(type(self._instruction) is str):
			state._previous_edge = self

	"""def __repr__(self):
		return "(%s, %s)" % (self._condition, self._target_state)"""

class CFG(object):
	"""
	This class represents a symbolic control flow graph.
	"""

	def __init__(self):
		self.vertices = []
		self.edges = []
		empty_vertex = CFGVertex('')
		self.vertices.append(empty_vertex)
		self.starting_vertices = empty_vertex

	def process_block(self, block, starting_vertices=None, condition=[]):
		"""
		Given a block, a set of starting vertices and to put on the first edge,
		construct the section of the control flow graph corresponding to this block.
		"""
		current_vertices = starting_vertices if not(starting_vertices is None) else [self.starting_vertices]

		print("starting vertices %s" % starting_vertices)

		print("processing block", block)

		for (n, entry) in enumerate(block):
			if type(entry) is ast.Assign or (type(entry) is ast.Expr and hasattr(entry.value, "func")):
				condition_to_use = condition if n == 0 else []
				# for each vertex in current_vertices, add an edge
				new_edges = []
				for vertex in current_vertices:
					entry._parent_body = block
					new_edge = CFGEdge(condition_to_use, entry)
					new_edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)
				# create a new vertex for the state created here
				new_vertex = None
				if type(entry) is ast.Assign:
					print("adding vertex for change of value for name %s" % entry.targets[0].id)
					new_vertex = CFGVertex(entry.targets[0].id)
				elif type(entry) is ast.Expr:
					#print("expression triggered", entry.value.__dict__)
					# only deal with function calls
					if hasattr(entry.value, "func"):
						print("adding vertex for result of function call of %s" % entry.value.func.id)
						new_vertex = CFGVertex(entry.value.func.id)

				self.vertices.append(new_vertex)
				self.edges += new_edges
				# direct all new edges to this new vertex
				for edge in new_edges:
					edge.set_target_state(new_vertex)

				# update current vertices
				current_vertices = [new_vertex]

			elif type(entry) is ast.If:
				# compute a list of pairs (condition, block) derived from the conditional
				pairs = [([entry.test], entry.body)]

				# need to accumulate conditions at some point

				#print(entry.orelse[0].orelse[0].__dict__)

				current_condition_set = [formula_tree.lnot(entry.test)]

				current_conditional = [entry]
				# won't work when there is something after the second if in the else clause
				while type(current_conditional[0]) is ast.If:
					current_conditional = current_conditional[0].orelse
					if len(current_conditional) > 0:
						if type(current_conditional[0]) is ast.If:
							pairs.append((current_condition_set + [current_conditional[0].test], current_conditional[0].body))
							current_condition_set.append(formula_tree.lnot(current_conditional[0].test))
						else:
							pairs.append((current_condition_set, current_conditional))
					else:
						# nowhere else to go in the traversal
						break

				print(pairs)

				# add the branches to the graph
				final_conditional_vertices = []
				for pair in pairs:
					final_vertices = self.process_block(pair[1], current_vertices, pair[0])
					final_conditional_vertices += final_vertices
					#vertices += final_vertices

				current_vertices = final_conditional_vertices

			elif type(entry) is ast.For:

				# process loop body
				final_vertices = self.process_block(entry.body, current_vertices, ['for'])

				print("final vertex in loop", current_vertices[0].edges[0]._target_state)

				# add 2 edges from the final_vertex - one going back to the start of the loop
				# with the positive condition, and one going to the next vertex
				# though addition of the first is done automatically

				for final_vertex in final_vertices:
					for base_vertex in current_vertices:
						new_positive_edge = CFGEdge('for', 'loop-jump')
						self.edges.append(new_positive_edge)
						final_vertex.add_outgoing_edge(new_positive_edge)
						new_positive_edge.set_target_state(base_vertex)

				current_vertices = final_vertices

		print("finished processing block")

		return current_vertices

	def next_calls(self, vertex, function, calls=[], marked_vertices=[]):
		"""
		Given a vertex, find the set of next edges that model calls to function.
		"""
		print("marked vertices are %s" % marked_vertices)
		if not(vertex in marked_vertices):
			print("vertex %s not visited" % vertex)
			marked_vertices.append(vertex)
			edges = vertex.edges
			for edge in edges:
				if (type(edge._instruction) is ast.Expr
					and hasattr(edge._instruction.value, "func")
					and edge._instruction.value.func.id == function):
					print("edge calling %s is counted" % edge._instruction.value.func.id)
					calls.append(edge)
				else:
					# this edge is not what we're looking for
					# so traverse this branch further
					print("recursing on vertex that changes %s" % edge._target_state._name_changed)
					self.next_calls(edge._target_state, function, calls, marked_vertices)
		else:
			print("vertex %s already visited" % vertex)

def expression_as_string(expression):
	if type(expression) is ast.Num:
		return str(expression.n)
	else:
		return str(expression)

def instruction_to_string(instruction):
	if type(instruction) is ast.Assign:
		return "%s = %s" % (instruction.targets[0].id, expression_as_string(instruction.value))
	elif type(instruction) is ast.Expr:
		return "%s()" % (instruction.value.func.id)