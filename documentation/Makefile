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

QUERYCERTDOTIO=../../querycert.github.io


#
CP=cp

## Deploy documentation
all:
	make -C .. docs

deploy:
	$(CP) qcertsite.css $(QUERYCERTDOTIO)
	$(CP) index.html $(QUERYCERTDOTIO)
	$(CP) demo.html $(QUERYCERTDOTIO)
	$(CP) doc.html $(QUERYCERTDOTIO)
	mkdir -p $(QUERYCERTDOTIO)/figure
	$(CP) figure/figure.svg figure/figure.png figure/figure.pdf $(QUERYCERTDOTIO)/figure
	$(CP) html/* $(QUERYCERTDOTIO)/html
	@echo ""
	@echo "To push changes to the external Web site, you still need to do:"
	@echo "  cd $(QUERYCERTDOTIO) ; git commit -am \"Refresh to Web Site\" "
