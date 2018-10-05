"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

def f(n):
	import time
	#print("f is executing - sleeping for %f seconds" % n)
	time.sleep(n)

a = 10
for i in range(10):
	if i < 3:
		f(0.1)
	else:
		f(1.1)

g(50)