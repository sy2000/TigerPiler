SHELL:=/bin/bash

all:
	ml-build sources.cm Main.main test-image

run:
	@for i in `ls /home/shlomi/Downloads/tiger/testcases/test*` ; do \
		./run_test $i; \
	done
	

