"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

authenticated=1
if authenticated:
    existing_locks = query("get locks", [])
    if len(existing_locks) > 0:
    	# do nothing
    	print("LOCKS EXIST")
        pass
    else:
    	print("NO LOCKS EXIST")
        lock = new_lock()
        query("write", [lock])
else:
	# do nothing
    pass