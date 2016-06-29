QCERTCOMP=../bin/CACo
QCERTEVAL=../bin/CAEv

all:
	$(MAKE) all-javascript
	$(MAKE) all-java

all-javascript:
	$(QCERTCOMP) -source OQL -target JS oql/*.oql

all-java:
	$(QCERTCOMP) -source OQL -target Java oql/*.oql

clean:
	@rm -f oql/*.js
	@rm -f oql/*.java
