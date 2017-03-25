#!/bin/bash

DO_LOOP="no"

python3.5 -V > /dev/null 2>&1 || {
    echo >&2 "Python 3.5 doesn't seem to be installed.  Do you have a weird installation?"
    echo >&2 "If you have python 3.5, use it to run run.py instead of this script."
    exit 1; }

python3.5 run.py

LOOPS=0

set +e
while [ "$LOOPS" -eq 0 ] || [ "$DO_LOOP" == "yes" ]; do
	if [ "$DO_LOOP" == "yes" ]; then
		python3.5 run.py $@
	else
                python3.5 run.py $@
	fi
	if [ "$DO_LOOP" == "yes" ]; then
		if [ ${LOOPS} -gt 0 ]; then
			echo "Restarted $LOOPS times"
		fi 
		echo "To escape the loop, press CTRL+C now. Otherwise, wait 5 seconds for the server to restart."
		echo ""
		sleep 5
		((LOOPS++))
	fi
done
