all:
	@echo "need to \"make run\" or \"make harvest\""

.PHONY: run
run:
#	mv -f harvest-howto.sh /tmp
#	./run ctl-pldi13small-nla-rest run ddr
#	./run ctl-nla1 run ddr
#	./run ctl run ddr
#	./run ctl-pldi13small-nla-rest run t2,function
#	./run ctl-nla1 run t2,function
#	./run ctl run t2
	./run ctl run function

.PHONY: harvest
harvest:
	sh harvest-howto.sh

#	./run --iters=1 --prop=termination --harvest=true ltl-test-lin run ultimate