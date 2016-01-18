barshare.js: barshare.hs
	hastec -Wall -fno-warn-unused-do-bind barshare.hs

clean:
	rm -r main barshare.js barshare.o barshare.hi
