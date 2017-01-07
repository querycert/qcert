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

COQDOCFLAGS=-interpolate -utf8 --lib-subtitles --no-lib-name -l
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
	Basic/BasicTypes \
	Basic/BasicSystem \
	Basic/TypingRuntime \
	NRA/Algebra/RAlg \
	NRA/Algebra/RAlgSugar \
	NRA/Algebra/RAlgSize \
	NRA/Algebra/RAlgEq \
	NRA/Algebra/RAlgExt \
	NRA/Algebra/RAlgExtEq \
	NRA/Typing/TAlg \
	NRA/Typing/TAlgInfer \
        NRA/Typing/TAlgEq \
        NRA/Typing/TAlgExt \
        NRA/Typing/TDomain \
	NRA/Context/RAlgContext \
	NRA/NRARuntime \
	NRA/NRATypes \
	NRA/NRASystem \
	NRA/Optim/NRARewrite \
	NRA/Optim/NRARewriteContext \
	NRA/Optim/NRAExtRewrite \
	NRA/Optim/TNRARewrite \
	NRA/NRAOptim \
	NRAEnv/Algebra/RAlgEnv \
	NRAEnv/Algebra/RAlgEnvSize \
	NRAEnv/Algebra/RAlgEnvIgnore \
	NRAEnv/Algebra/RAlgEnvEq \
        NRAEnv/Extended/NRAEnv \
        NRAEnv/Extended/NRAEnvSize \
        NRAEnv/Extended/NRAEnvEq \
        NRAEnv/Extended/NRAEnvIgnore \
	NRAEnv/Typing/TAlgEnv \
	NRAEnv/Typing/TAlgEnvInfer \
	NRAEnv/Typing/TAlgEnvIgnore \
        NRAEnv/Typing/TAlgEnvEq \
	NRAEnv/Typing/TNRAEnv \
	NRAEnv/Typing/TNRAEnvEq \
	NRAEnv/NRAEnvRuntime \
	NRAEnv/NRAEnvTypes \
	NRAEnv/NRAEnvSystem \
	NRAEnv/Context/RAlgEnvContext \
	NRAEnv/Context/RAlgEnvContextLift \
	NRAEnv/Optim/NRAEnvRewrite \
	NRAEnv/Optim/NRAEnvRewriteContext \
	NRAEnv/Optim/TNRAEnvRewrite \
	NRAEnv/Optim/NRAEnvOptimizer \
	NRAEnv/NRAEnvOptim \
	NNRC/Calculus/NNRC \
	NNRC/Calculus/NNRCShadow \
	NNRC/Calculus/NNRCNorm \
	NNRC/Calculus/NNRCEq \
	NNRC/Calculus/NNRCSize \
	NNRC/Extended/NNRCExt \
	NNRC/Extended/NNRCExtShadow \
	NNRC/Extended/NNRCExtEq \
	NNRC/Typing/TNNRC \
	NNRC/Typing/TNNRCExt \
	NNRC/Typing/TNNRCInfer \
	NNRC/Typing/TNNRCEq \
	NNRC/Typing/TNNRCExtEq \
	NNRC/Typing/TNNRCShadow \
	NNRC/Typing/TNNRCExtShadow \
	NNRC/NNRCRuntime \
	NNRC/NNRCTypes \
	NNRC/NNRCSystem \
	NNRC/Optim/NNRCRewriteUtil \
	NNRC/Optim/NNRCRewrite \
	NNRC/Optim/TNNRCRewrite \
	NNRC/Optim/NNRCOptimizer \
	NNRC/Optim/TNNRCOptimizer \
	NNRC/NNRCOptim \
	NNRCMR/Calculus/ForeignReduceOps \
	NNRCMR/Calculus/NNRCMR \
	NNRCMR/NNRCMRRuntime \
	NNRCMR/Optim/NNRCMRRewrite \
	NNRCMR/Optim/TNNRCMROptimizer \
	NNRCMR/NNRCMROptim \
	DNNRC/Calculus/DNNRC \
	DNNRC/Calculus/DNNRCSize \
	DNNRC/Calculus/DNNRCEq \
	DNNRC/Calculus/Dataset \
	DNNRC/Calculus/DatasetSize \
	DNNRC/Typing/TDNRC \
	DNNRC/Typing/TDNRCsub \
	DNNRC/Typing/TDNRCInfer \
	DNNRC/Typing/TOpsInferSub \
	DNNRC/Optim/DNNRCOptimizer \
	CAMP/Core/CAMP \
	CAMP/Core/CAMPSize \
	CAMP/Core/CAMPSugar \
	CAMP/Typing/TCAMP \
	CAMP/Typing/TCAMPSugar \
	CAMP/CAMPRuntime \
	CAMP/CAMPTypes \
	CAMP/CAMPSystem \
	Rule/Core/Rule \
	Rule/Core/RuleSugar \
	Rule/Typing/TRule \
	Rule/RuleRuntime \
	Rule/RuleTypes \
	Rule/RuleSystem \
	CldMR/CldMRUtil \
	CldMR/ForeignCloudant \
	CldMR/CldMR \
	LambdaNRA/LambdaNRA \
	LambdaNRA/LambdaNRASugar \
	LambdaNRA/LambdaNRAEq \
	SQL/SQL \
	SQL/SQLSize \
	OQL/Lang/OQL \
	OQL/Lang/OQLSugar \
	OQL/Lang/OQLSize \
	OQL/Typing/TOQL \
	OQL/OQLRuntime \
	OQL/OQLTypes \
	OQL/OQLSystem \
	Translation/ForeignToReduceOps \
	Translation/ForeignToCloudant \
	Translation/NRAtoNNRC \
	Translation/NRAEnvtoNNRC \
	Translation/NRAEnvtoNNRCExt \
	Translation/NNRCtoCAMP \
	Translation/NNRCtoNNRCMR \
	Translation/NNRCtoDNNRC \
	Translation/NNRCMRtoNNRC \
	Translation/NNRCMRtoDNNRC \
	Translation/NNRCMRtoCldMR \
	Translation/CAMPtoNRA \
	Translation/CAMPtoNRAEnv \
	Translation/CAMPSugartoNRA \
	Translation/CAMPSugartoNRAEnv \
	Translation/RuletoNRA \
	Translation/RuletoNRAEnv \
	Translation/TNRAtoNNRC \
	Translation/TNRAEnvtoNNRC \
	Translation/TNNRCtoCAMP \
	Translation/TCAMPtoNRA \
	Translation/TCAMPtoNRAEnv \
	Translation/LambdaNRAtoNRAEnv \
	Translation/SQLtoNRAEnv \
	Translation/OQLtoNRAEnv \
	Translation/TOQLtoNRAEnv \
	Backend/JSON \
	Backend/ForeignToJSON \
	Backend/ForeignTypeToJSON \
	Backend/ForeignToJava \
	Backend/ForeignToJavascript \
	Backend/ForeignToScala \
	Backend/ForeignToSpark \
	Backend/JSONtoData \
	Backend/NNRCtoJava \
	Backend/NNRCtoJavascript \
	Backend/NNRCMRtoSpark \
	Backend/CldMRtoJavaScript \
	Backend/SparkData \
	Backend/DNNRCtoScala \
	Compiler/CompilerModel/CompilerRuntime \
	Compiler/CompilerModel/CompilerModel \
	Compiler/CompilerModel/FloatModelPart \
	Compiler/CompilerModel/StringModelPart \
	Compiler/CompilerModel/DateTimeModelPart \
	Compiler/CompilerModel/SqlDateModelPart \
	Compiler/CompilerModel/EnhancedModel \
	Compiler/CompilerModel/TrivialModel \
	Compiler/CompilerDriver/CompLang \
	Compiler/CompilerDriver/CompEnv \
	Compiler/CompilerDriver/CompConfig \
	Compiler/CompilerDriver/CompDriver \
	Compiler/CompilerDriver/CompStat \
	Compiler/CompilerDriver/CompEval \
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
	Tests/TNRATest \
	Tests/CAMPTest \
	Tests/TCAMPTest \
	Tests/CompilerTest \
	Tests/OQLTest \
	Tests/SQLTest \
	Tests/LambdaNRATests

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
	@coq_makefile -R coq Qcert $(FILES) -o Makefile.coq

html: Makefile.coq
	@$(MAKE) -f Makefile.coq html

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

HTML=index.html

index.html: index.v
	@rm -f index.html
	coqdoc -l -s --no-index index.v

.PHONY: all clean clean_detritus html

