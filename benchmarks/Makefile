all:
	@echo "need to \"make run\" or \"make harvest\""

.PHONY: run
run:
#	mv -f harvest-howto.sh /tmp
	./run ctl-pldi13small-nla-rest run ddr
	./run ctl-pldi13small-nla run ddr
	./run ctl-svcomp run ddr
	./run ctl-pldi13small-nla-rest run t2,function
	./run ctl-pldi13small-nla run t2,function
	./run ctl-svcomp run t2,function

.PHONY: harvest
harvest:
	sh harvest-howto.sh

.PHONY: publish
publish:
	git add results/*.tex
	git commit -m "Updated results tex" results/*.tex
	git push
#	./run --iters=1 --prop=termination --harvest=true ltl-test-lin run ultimate