# 
#  Copyright (C) 2017 Joshua Auerbach 
# 
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
# 
#  http://www.apache.org/licenses/LICENSE-2.0
# 
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
# 
ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

JAVA_SRCS=$(wildcard src/org/qcert/sql/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

# Keep this list accurate as dependencies evolve or versions change
DEPENDENCIES=lib/antlr4-runtime-4.5.3.jar \
	     lib/presto-parser-0.154.jar \
	     lib/presto-parser-0.154-sources.jar \
	     lib/slice-0.7.jar \
	     lib/guava-19.0.jar \
	     lib/guava-19.0-sources.jar
CPATH=$(subst $(BLANK),$(PATH_SEP),../javaService/bin ../javaService/lib/gson-2.7.jar $(DEPENDENCIES))

JAVAC=javac

all:
	$(MAKE) -C ../javaService all
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

cleanall: clean
	@rm -f $(DEPENDENCIES)

