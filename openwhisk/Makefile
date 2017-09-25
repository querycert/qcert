all: deploy

init:
	npm install

compile:
	./node_modules/.bin/tsc


deploy: compile
	$(MAKE) -C ../javaService whisk_deploy
	./tools/cli/deploy

undeploy:
	- ./tools/cli/undeploy
	$(MAKE) -C ../javaService whisk_undeploy

tests:

clean:
	rm -rf _build

cleanall: undeploy clean
	rm -rf *~

realcleanall: cleanall
	rm -rf node_modules package-lock.json

.PHONY: init compile deploy undeploy tests clean cleanall realcleanall
