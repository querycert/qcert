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

FILES = $(MODULES:%=%.v)

gather_globs:
	@find . \( -name '*.glob' \) -print0 | xargs -0 ../scripts/gather_glob.sh

documentation: $(FILES)
	@$(MAKE) gather_globs
	mkdir -p ../docs/html
	rm -f ../docs/html/*.html
	../$(COQ2HTML)/coq2html -d ../docs/html -base Qcert ../docs/globs/*.glob $^
	cp ../docs/coq2html.css ../docs/coq2html.js ../docs/html/

.PHONY: all clean clean_detritus html
