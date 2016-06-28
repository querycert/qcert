export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF-8
OSTYPE=$(shell uname -o)

JAVA_SRCS=src/JAPITest.java $(wildcard src/org/qcert/calib/*.java)
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

RAWCPATH=bin $(wildcard ../../lib/*.jar)
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

all:
	$(MAKE) classes

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

clean:
	-rm -fr bin/*
	-rm -f *~

.PRECIOUS: bin/*/*.class bin/*/*/*.class
