"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

from threading import Lock

class VerdictReport(object):
	"""
	Maintains a map from binding space indices to sets of verdicts reached at runtime.
	"""

	def __init__(self):
		self._bind_space_to_verdicts = {}
		self.map_lock = Lock()

	def add_verdict(self, bind_space_index, verdict):
		self.map_lock.acquire()
		if not(self._bind_space_to_verdicts.get(bind_space_index)):
			self._bind_space_to_verdicts[bind_space_index] = [verdict]
		else:
			self._bind_space_to_verdicts[bind_space_index].append(verdict)
		self.map_lock.release()

	def get_final_verdict_report(self):
		return self._bind_space_to_verdicts