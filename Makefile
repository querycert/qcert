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

CP=cp
TSC?=tsc

# This may have to be specialized
COQ2HTML=../../opt/bin
COQDOCFLAGS=-interpolate -utf8 --lib-subtitles --no-lib-name -l
export COQ2HTML
export COQDOCFLAGS

DIST_DIR=

#	Basic/Util/RTactics
MODULES = \
	Basic/Util/Digits \
	Basic/Util/Lattice \
	Basic/Util/Monoid \
	Basic/Util/RUtil \
	Basic/Util/RLift \
	Basic/Util/RList \
	Basic/Util/RSort \
	Basic/Util/RString \
	Basic/Util/RAssoc \
	Basic/Util/RSublist \
	Basic/Util/RCompat \
	Basic/Util/RFresh \
	Basic/Util/RBindings \
	Basic/Util/RBindingsNat \
	Basic/Util/Utils \
	Basic/Logger/OptimizerStep \
	Basic/Logger/OptimizerLogger \
	Basic/Data/RBag \
	Basic/Data/RDomain \
	Basic/Data/BrandRelation \
	Basic/Data/ForeignData \
	Basic/Data/RData \
	Basic/Data/RDataNorm \
	Basic/Data/RRelation \
	Basic/Data/RDataSort \
	Basic/Data/RGroupBy \
	Basic/Data/DData \
	Basic/Data/DDataNorm \
	Basic/Env/RConstants \
	Basic/Env/DConstants \
	Basic/Operators/RUtilOps \
	Basic/Operators/ForeignOps \
	Basic/Operators/RUnaryOps \
	Basic/Operators/RUnaryOpsSem \
	Basic/Operators/RBinaryOps \
	Basic/Operators/RBinaryOpsSem \
	Basic/Operators/ROpsEq \
	Basic/Operators/ROps \
	Basic/ForeignRuntime \
	Basic/BasicRuntime \
	Basic/TypeSystem/ForeignType \
	Basic/TypeSystem/RType \
	Basic/TypeSystem/RTypeNorm \
	Basic/TypeSystem/DType \
        Basic/TypeSystem/TBrandContext \
	Basic/TypeSystem/RSubtype \
	Basic/TypeSystem/RSubtypeProp \
	Basic/TypeSystem/RTypeMeetJoin \
	Basic/TypeSystem/RConsistentSubtype \
	Basic/TypeSystem/TBrandModel \
	Basic/TypeSystem/RTypeLattice \
	Basic/TypeSystem/TBrandModelProp \
	Basic/TypeSystem/Types \
	Basic/Typing/ForeignDataTyping \
	Basic/Typing/TUtil \
	Basic/Typing/TData \
	Basic/Typing/TDData \
	Basic/Typing/TBindings \
	Basic/Typing/TDBindings \
	Basic/Typing/ForeignOpsTyping \
	Basic/Typing/TDataInfer \
	Basic/Typing/TDataSort \
	Basic/Typing/TOps \
	Basic/Typing/TOpsEq \
	Basic/Typing/TOpsInfer \
	Basic/ForeignTyping \
	Basic/JSON/JSON \
	Basic/JSON/ForeignToJSON \
	Basic/JSON/ForeignTypeToJSON \
	Basic/JSON/JSONtoData \
	Basic/BasicTypes \
	Basic/BasicSystem \
	Basic/TypingRuntime \
	NRA/Lang/NRA \
	NRA/Lang/NRASugar \
	NRA/Lang/NRASize \
	NRA/Lang/NRAEq \
	NRA/Lang/NRAExt \
	NRA/Lang/NRAExtEq \
	NRA/Typing/TNRA \
	NRA/Typing/TNRAInfer \
        NRA/Typing/TNRAEq \
        NRA/Typing/TNRAExt \
        NRA/Typing/TDomain \
	NRA/Context/NRAContext \
	NRA/NRARuntime \
	NRA/NRATypes \
	NRA/NRASystem \
	NRA/Optim/NRARewrite \
	NRA/Optim/NRARewriteContext \
	NRA/Optim/NRAExtRewrite \
	NRA/Optim/TNRARewrite \
	NRA/NRAOptim \
	NRAEnv/Core/cNRAEnv \
	NRAEnv/Core/cNRAEnvSize \
	NRAEnv/Core/cNRAEnvIgnore \
	NRAEnv/Core/cNRAEnvEq \
        NRAEnv/Lang/NRAEnv \
        NRAEnv/Lang/NRAEnvSize \
        NRAEnv/Lang/NRAEnvEq \
        NRAEnv/Lang/NRAEnvIgnore \
	NRAEnv/Typing/TcNRAEnv \
	NRAEnv/Typing/TcNRAEnvInfer \
	NRAEnv/Typing/TcNRAEnvIgnore \
        NRAEnv/Typing/TcNRAEnvEq \
	NRAEnv/Typing/TNRAEnv \
	NRAEnv/Typing/TNRAEnvEq \
	NRAEnv/NRAEnvRuntime \
	NRAEnv/NRAEnvTypes \
	NRAEnv/NRAEnvSystem \
	NRAEnv/Context/cNRAEnvContext \
	NRAEnv/Context/cNRAEnvContextLift \
	NRAEnv/Optim/NRAEnvRewrite \
	NRAEnv/Optim/NRAEnvRewriteContext \
	NRAEnv/Optim/TNRAEnvRewrite \
	NRAEnv/Optim/NRAEnvOptimizer \
	NRAEnv/NRAEnvOptim \
	NNRC/Core/cNNRC \
	NNRC/Core/cNNRCShadow \
	NNRC/Core/cNNRCNorm \
	NNRC/Core/cNNRCEq \
	NNRC/Lang/NNRC \
	NNRC/Lang/NNRCSugar \
	NNRC/Lang/NNRCShadow \
	NNRC/Lang/NNRCEq \
	NNRC/Lang/NNRCSize \
	NNRC/Typing/TcNNRC \
	NNRC/Typing/TNNRC \
	NNRC/Typing/TcNNRCInfer \
	NNRC/Typing/TcNNRCEq \
	NNRC/Typing/TNNRCEq \
	NNRC/Typing/TcNNRCShadow \
	NNRC/Typing/TNNRCShadow \
	NNRC/NNRCRuntime \
	NNRC/NNRCTypes \
	NNRC/NNRCSystem \
	NNRC/Optim/NNRCRewriteUtil \
	NNRC/Optim/NNRCRewrite \
	NNRC/Optim/TNNRCRewrite \
	NNRC/Optim/NNRCOptimizer \
	NNRC/NNRCOptim \
	NNRCMR/Lang/ForeignReduceOps \
	NNRCMR/Lang/NNRCMR \
	NNRCMR/NNRCMRRuntime \
	NNRCMR/NNRCMRSystem \
	NNRCMR/Optim/NNRCMRRewrite \
	NNRCMR/Optim/NNRCMROptimizer \
	NNRCMR/NNRCMROptim \
	DNNRC/Lang/DNNRC \
	DNNRC/Lang/DNNRCSize \
	DNNRC/Lang/DNNRCEq \
	DNNRC/Lang/Dataset \
	DNNRC/Lang/DatasetSize \
	DNNRC/Lang/DNNRCDataset \
	DNNRC/Typing/TDNNRC \
	DNNRC/Typing/TDNNRCSub \
	DNNRC/Typing/TOpsInferSub \
	DNNRC/Typing/TDNNRCInfer \
	DNNRC/Typing/TDNNRCDataset \
	DNNRC/DNNRCRuntime \
	DNNRC/DNNRCTypes \
	DNNRC/DNNRCSystem \
	DNNRC/Optim/tDNNRCOptimizer \
	DNNRC/DNNRCOptim \
	CAMP/Lang/CAMPUtil \
	CAMP/Lang/CAMP \
	CAMP/Lang/CAMPSize \
	CAMP/Lang/CAMPSugar \
	CAMP/Typing/TCAMP \
	CAMP/Typing/TCAMPSugar \
	CAMP/CAMPRuntime \
	CAMP/CAMPTypes \
	CAMP/CAMPSystem \
	CAMPRule/Lang/CAMPRule \
	CAMPRule/Lang/CAMPRuleSugar \
	CAMPRule/Typing/TCAMPRule \
	CAMPRule/CAMPRuleRuntime \
	CAMPRule/CAMPRuleTypes \
	CAMPRule/CAMPRuleSystem \
	TechRule/Lang/TechRule \
	TechRule/TechRuleRuntime \
	DesignRule/Lang/DesignRule \
	DesignRule/DesignRuleRuntime \
	CldMR/Lang/CldMRUtil \
	CldMR/Lang/ForeignCloudant \
	CldMR/Lang/CldMR \
	CldMR/CldMRRuntime \
	CldMR/CldMRSystem \
	LambdaNRA/Lang/LambdaNRA \
	LambdaNRA/Lang/LambdaNRASugar \
	LambdaNRA/Lang/LambdaNRAEq \
	LambdaNRA/LambdaNRARuntime \
	LambdaNRA/LambdaNRASystem \
	SQL/Lang/SQL \
	SQL/Lang/SQLSize \
	SQL/SQLRuntime \
	SQL/SQLSystem \
	OQL/Lang/OQL \
	OQL/Lang/OQLSugar \
	OQL/Lang/OQLSize \
	OQL/Typing/TOQL \
	OQL/OQLRuntime \
	OQL/OQLTypes \
	OQL/OQLSystem \
	JavaScript/Lang/JavaScript \
	JavaScript/JavaScriptRuntime \
	Java/Lang/Java \
	Java/JavaRuntime \
	SparkRDD/Lang/SparkRDD \
	SparkRDD/SparkRDDRuntime \
	SparkDF/Lang/SparkDF \
	SparkDF/SparkDFRuntime \
	Cloudant/Lang/Cloudant \
	Cloudant/CloudantRuntime \
	Translation/ForeignToReduceOps \
	Translation/ForeignToCloudant \
	Translation/NRAtocNNRC \
	Translation/cNRAEnvtocNNRC \
	Translation/cNRAEnvtoNRA \
	Translation/NRAtocNRAEnv \
	Translation/NRAEnvtoNNRC \
	Translation/cNNRCtoCAMP \
	Translation/NNRCtoNNRCMR \
	Translation/NNRCtoDNNRC \
	Translation/NNRCMRtoNNRC \
	Translation/NNRCMRtoDNNRC \
	Translation/NNRCMRtoCldMR \
	Translation/DNNRCtotDNNRC \
	Translation/CAMPRuletoCAMP \
	Translation/TechRuletoCAMP \
	Translation/DesignRuletoCAMP \
	Translation/CAMPtoNRA \
	Translation/CAMPtocNRAEnv \
	Translation/CAMPtoNRAEnv \
	Translation/TNRAtocNNRC \
	Translation/TcNRAEnvtocNNRC \
	Translation/TcNNRCtoCAMP \
	Translation/TCAMPtoNRA \
	Translation/TCAMPtocNRAEnv \
	Translation/TCAMPtoNRAEnv \
	Translation/LambdaNRAtoNRAEnv \
	Translation/SQLtoNRAEnv \
	Translation/OQLtoNRAEnv \
	Translation/TOQLtoNRAEnv \
	Translation/ForeignToJavaScript \
	Translation/ForeignToJava \
	Translation/ForeignToScala \
	Translation/ForeignToSpark \
	Translation/CldMRtoCloudant \
	Translation/NNRCtoJava \
	Translation/NNRCtoJavaScript \
	Translation/NNRCMRtoSparkRDD \
	Translation/DatatoSparkDF \
	Translation/tDNNRCtoSparkDF \
	Compiler/Model/CompilerRuntime \
	Compiler/Model/CompilerModel \
	Compiler/Model/FloatModelPart \
	Compiler/Model/StringModelPart \
	Compiler/Model/DateTimeModelPart \
	Compiler/Model/SqlDateModelPart \
	Compiler/Model/EnhancedModel \
	Compiler/Model/TrivialModel \
	Compiler/Driver/CompLang \
	Compiler/Driver/CompEnv \
	Compiler/Driver/CompConfig \
	Compiler/Driver/CompDriver \
	Compiler/Driver/CompStat \
	Compiler/Driver/CompEval \
	Compiler/QLib/QData \
	Compiler/QLib/QOperators \
	Compiler/QLib/QCAMP \
	Compiler/QLib/QRule \
	Compiler/QLib/QOQL \
	Compiler/QLib/QSQL \
	Compiler/QLib/QLambdaNRA \
	Compiler/QLib/QLang \
	Compiler/QLib/QDriver \
	Compiler/QLib/QStat \
	Compiler/QLib/QUtil \
	Compiler/QLib/QEval \
	Compiler/QLib/QType \
	Compiler/QLib \
	Compiler/EnhancedCompiler \
	Compiler/TrivialCompiler \
	Compiler/CompilerExports \
	Tests/NRATest \
	Tests/NRAEnvTest \
	Tests/TNRATest \
	Tests/CAMPTest \
	Tests/TCAMPTest \
	Tests/CompilerTest \
	Tests/OQLTest \
	Tests/SQLTest \
	Tests/LambdaNRATest \
	Tests/TDataTest \
	Tests/DatasetTest

FILES = $(addprefix coq/,$(MODULES:%=%.v))

all:
	@$(MAKE) qcert
	@$(MAKE) extraction
	@$(MAKE) java-runtime
	@$(MAKE) spark2-runtime

java-runtime:
	@$(MAKE) -C runtime/java

spark2-runtime:
	@$(MAKE) -C runtime/spark2

japi:
	@$(MAKE) java-extraction
	@$(MAKE) lib/QcertLibrary.jar

demo: qcert jsapi
	@echo "[Qcert] "
	@echo "[Qcert] Compiling typescript files to javascript"
	@echo "[Qcert] "
	cd www && $(TSC) -p "tsconfig.json"

jsapi:
	@$(MAKE) js-extraction

lib/QcertLibrary.jar:
	ant -f scripts/makeQcertLibrary.xml

qcert: Makefile.coq
	@echo "[Qcert] "
	@echo "[Qcert] Compiling Coq source"
	@echo "[Qcert] "
	@$(MAKE) -f Makefile.coq

extraction:
	@echo "[Qcert] "
	@echo "[Qcert] Extracting compiler to OCaml"
	@echo "[Qcert] "
	@$(MAKE) -C ocaml realclean all

java-extraction:
	@echo "[Qcert] "
	@echo "[Qcert] Extracting compiler to OCaml + Java"
	@echo "[Qcert] "
	@$(MAKE) -C ocaml clean japi

js-extraction:
	@echo "[Qcert] "
	@echo "[Qcert] Extracting compiler to OCaml + Javascript"
	@echo "[Qcert] "
	@$(MAKE) -C ocaml js

Makefile.coq: Makefile $(VS) $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

html: Makefile.coq
	@$(MAKE) -f Makefile.coq html

gather_globs:
	@find ./coq \( -name '*.glob' \) -print0 | xargs -0 ./scripts/gather_glob.sh

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 ./script/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

clean:: Makefile.coq remove_all_derived
	@$(MAKE) -f Makefile.coq clean
	@$(MAKE) -C ocaml realclean
	@$(MAKE) -C runtime/java clean
	@$(MAKE) -C runtime/spark2 clean
	@$(MAKE) -C samples clean
	@rm -f Makefile.coq
	@rm -f *~
	@rm -f index.html

cleanall: clean remove_all_derived clean_detritus

DISTDIR=../qcert-0.1.0

$(DISTDIR):
	@cp -R ../qcert $(DISTDIR)
	@rm -rf $(DISTDIR)/.git
	@$(MAKE) -C $(DISTDIR) clean remove_all_derived

dist:
	$(MAKE) $(DISTDIR)
	tar cvf $(DISTDIR).tar $(DISTDIR)
	gzip $(DISTDIR).tar

cleandist:
	rm -rf $(DISTDIR)
	rm -f $(DISTDIR).tar.gz

documentation: $(COQ2HTML)/coq2html $(FILES)
	@$(MAKE) gather_globs
	mkdir -p docs/html
	rm -f docs/html/*.html
	$(COQ2HTML)/coq2html -top-dir coq -o 'docs/html/%.html' docs/globs/*.glob \
          $(filter-out $(COQ2HTML)/coq2html, $^)
	cp docs/coq2html.css docs/coq2html.js docs/html/

.PHONY: all clean clean_detritus html
