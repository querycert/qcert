export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF-8
OSTYPE=$(shell uname -o)

JAVA_SRCS=$(wildcard src/org/qcert/sql/*.java)
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

# Keep this list accurate as dependencies evolve or versions change
DEPENDENCIES=lib/antlr4-runtime-4.5.3.jar lib/presto-parser-0.161.jar \
    lib/slice-0.7.jar lib/guava-19.0.jar lib/nanohttpd-2.3.1.jar
CPATH=$(subst $(BLANK),$(PATH_SEP),$(DEPENDENCIES))

JAVAC=javac

all:
	$(MAKE) classes
	ant -f export.xml

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(DEPENDENCIES):
	ant -f getDependencies.xml

clean:
	@rm -rf bin/*
