#
# Copyright 2015-2016 IBM Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF-8
OSTYPE=$(shell uname -o)

JAVA_SRCS=src/JavaTestRunner.java $(wildcard src/org/qcert/runtime/*.java)
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

RAWCPATH=bin $(wildcard lib/*.jar)
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
