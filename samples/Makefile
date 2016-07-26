export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF-8
OSTYPE=$(shell uname -o)

JAVA_SRCS=$(wildcard src/testing/runners/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

ifeq ($(OSTYPE),Cygwin)
  PATH_SEP=';'
else
  ifeq ($(OSTYPE),Msys)
    PATH_SEP=';'
  else
    PATH_SEP=':'
  endif
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

RAWCPATH=bin
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))



QCERTCOMP=../bin/CACo
QCERTEVAL=../bin/CAEv

all:
	$(MAKE) all-javascript
	$(MAKE) all-java
	$(MAKE) classes

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

all-javascript:
	$(QCERTCOMP) -source OQL -target JS oql/*.oql

all-java:
	$(QCERTCOMP) -source OQL -target Java oql/*.oql

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java

