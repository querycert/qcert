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

JAVA_SRCS=$(wildcard src/org/qcert/javasvc/*.java src/org/qcert/util/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

# Keep this list accurate as dependencies evolve or versions change
DEPENDENCIES=lib/nanohttpd-2.3.1.jar \
	     lib/nanohttpd-2.3.1-sources.jar \
	     lib/gson-2.7.jar \
	     lib/gson-2.7-sources.jar \
	     lib/commons-csv-1.1.jar \
	     lib/commons-csv-1.1-sources.jar \
	     lib/httpclient-4.5.2.jar \
	     lib/httpclient-4.5.2-sources.jar \
	     lib/httpcore-4.4.5.jar \
	     lib/httpcore-4.4.5-sources.jar \
	     lib/commons-logging-1.2.jar
CPATH=$(subst $(BLANK),$(PATH_SEP),$(DEPENDENCIES))

JAVAC=javac

# Default target just builds the code
all:
	$(MAKE) classes

# Install target must execute AFTER various services (statically dependent on this code) have been built and exported	
install:
	ant -f export.xml

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(DEPENDENCIES):
	ant -f getDependencies.xml

clean:
	@rm -rf bin/*
	@rm -f javaService.zip

cleanall: clean
	@rm -f $(DEPENDENCIES)
	@rm -f services/*.jar

