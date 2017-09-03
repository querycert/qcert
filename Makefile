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

include Makefile.config

#
CP=cp
TSC?=tsc

export MODULES = \
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
	Basic/Env/RVar \
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
	Basic/Typing/TOpsInferSub \
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
	cNRAEnv/Lang/cNRAEnv \
	cNRAEnv/Lang/cNRAEnvSize \
	cNRAEnv/Lang/cNRAEnvIgnore \
	cNRAEnv/Lang/cNRAEnvEq \
	cNRAEnv/Typing/TcNRAEnv \
	cNRAEnv/Typing/TcNRAEnvInfer \
	cNRAEnv/Typing/TcNRAEnvIgnore \
        cNRAEnv/Typing/TcNRAEnvEq \
        cNRAEnv/Context/cNRAEnvContext \
	cNRAEnv/Context/cNRAEnvContextLift \
	cNRAEnv/cNRAEnvRuntime \
	cNRAEnv/cNRAEnvTypes \
	cNRAEnv/cNRAEnvSystem \
	NRAEnv/Lang/NRAEnv \
        NRAEnv/Lang/NRAEnvSize \
        NRAEnv/Lang/NRAEnvEq \
        NRAEnv/Lang/NRAEnvIgnore \
	NRAEnv/Typing/TNRAEnv \
	NRAEnv/Typing/TNRAEnvEq \
	NRAEnv/NRAEnvRuntime \
	NRAEnv/NRAEnvTypes \
	NRAEnv/NRAEnvSystem \
	NRAEnv/Optim/NRAEnvRewrite \
	NRAEnv/Optim/NRAEnvRewriteContext \
	NRAEnv/Optim/TNRAEnvRewrite \
	NRAEnv/Optim/NRAEnvOptimizer \
	NRAEnv/NRAEnvOptim \
	cNNRC/Lang/cNNRC \
	cNNRC/Lang/cNNRCShadow \
	cNNRC/Lang/cNNRCNorm \
	cNNRC/Lang/cNNRCEq \
	cNNRC/Typing/TcNNRC \
	cNNRC/Typing/TcNNRCInfer \
	cNNRC/Typing/TcNNRCEq \
	cNNRC/Typing/TcNNRCShadow \
	cNNRC/cNNRCRuntime \
	cNNRC/cNNRCTypes \
	cNNRC/cNNRCSystem \
	NNRC/Lang/NNRC \
	NNRC/Lang/NNRCSugar \
	NNRC/Lang/NNRCShadow \
	NNRC/Lang/NNRCEq \
	NNRC/Lang/NNRCSize \
	NNRC/Typing/TNNRC \
	NNRC/Typing/TNNRCEq \
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
	DNNRC/Lang/DNNRCBase \
	DNNRC/Lang/DNNRCBaseSize \
	DNNRC/Lang/DNNRCBaseEq \
	DNNRC/Lang/Dataframe \
	DNNRC/Lang/DataframeSize \
	DNNRC/Lang/DNNRC \
	DNNRC/Typing/TDNNRCBase \
	DNNRC/DNNRCRuntime \
	DNNRC/DNNRCTypes \
	DNNRC/DNNRCSystem \
	tDNNRC/Lang/tDNNRC \
	tDNNRC/Typing/tDNNRCSub \
	tDNNRC/Typing/tDNNRCInfer \
	tDNNRC/tDNNRCRuntime \
	tDNNRC/tDNNRCTypes \
	tDNNRC/tDNNRCSystem \
	tDNNRC/Optim/tDNNRCOptimizer \
	tDNNRC/tDNNRCOptim \
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
	CldMR/Lang/CldMRSanitize \
	CldMR/CldMRRuntime \
	CldMR/CldMRSystem \
	LambdaNRA/Lang/LambdaNRA \
	LambdaNRA/Lang/LambdaNRASugar \
	LambdaNRA/Lang/LambdaNRAEq \
	LambdaNRA/Typing/TLambdaNRA \
	LambdaNRA/LambdaNRARuntime \
	LambdaNRA/LambdaNRATypes \
	LambdaNRA/LambdaNRASystem \
	SQL/Lang/SQL \
	SQL/Lang/SQLSize \
	SQL/SQLRuntime \
	SQL/SQLSystem \
	SQLPP/Lang/SQLPP \
	SQLPP/Lang/SQLPPSize \
	SQLPP/SQLPPRuntime \
	SQLPP/SQLPPSystem \
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
	Translation/cNRAEnvtoNRAEnv \
	Translation/NRAtocNRAEnv \
	Translation/NRAEnvtocNRAEnv \
	Translation/NRAEnvtoNNRC \
	Translation/cNNRCtoCAMP \
	Translation/cNNRCtoNNRC \
	Translation/NNRCtocNNRC \
	Translation/NNRCtoNNRCMR \
	Translation/NNRCtoDNNRC \
	Translation/NNRCMRtoNNRC \
	Translation/NNRCMRtoDNNRC \
	Translation/NNRCMRtoCldMR \
	Translation/DNNRCtotDNNRC \
	Translation/TechRuletoCAMPRule \
	Translation/DesignRuletoCAMPRule \
	Translation/CAMPRuletoCAMP \
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
	Translation/TLambdaNRAtoNRAEnv \
	Translation/SQLtoNRAEnv \
	Translation/SQLPPtoNRAEnv \
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
	Compiler/Driver/CompCorrectness \
	Compiler/QLib/QData \
	Compiler/QLib/QOperators \
	Compiler/QLib/QCAMP \
	Compiler/QLib/QCAMPRule \
	Compiler/QLib/QOQL \
	Compiler/QLib/QSQL \
	Compiler/QLib/QSQLPP \
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
	Tests/TDataTest \
	Tests/NRATest \
	Tests/NRAEnvTest \
	Tests/TNRATest \
	Tests/CAMPTest \
	Tests/TCAMPTest \
	Tests/tDNNRCTest \
	Tests/OQLTest \
	Tests/SQLTest \
	Tests/LambdaNRATest \
	Tests/CompilerTest

FILES = $(addprefix coq/,$(MODULES:%=%.v))

## Compiler
all:
	@$(MAKE) qcert

qcert: Makefile.coq
	@$(MAKE) qcert-coq
	@$(MAKE) qcert-ocaml
	@$(MAKE) qcert-javascript
	@$(MAKE) qcert-java
	@echo "[Q*cert] "
	@echo "[Q*cert] To compile the runtimes, do:"
	@echo "[Q*cert]   make qcert-runtimes"
	@echo "[Q*cert] "

qcert-coq: Makefile.coq
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Coq source"
	@echo "[Q*cert] "
	@$(MAKE) -f Makefile.coq

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) -C ocaml cleanall all

qcert-javascript:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to JavaScript"
	@echo "[Q*cert] "
	@$(MAKE) -C ocaml js

qcert-java:
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Java service"
	@echo "[Q*cert] "
	@$(MAKE) -C javaService
endif
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL support"
	@echo "[Q*cert] "
	@$(MAKE) -C sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL++ support"
	@echo "[Q*cert] "
	@$(MAKE) -C sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling ODM rules support"
	@echo "[Q*cert] "
	@$(MAKE) -C camp-java
	@$(MAKE) -C jrules2CAMP
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Deploying Java service"
	@echo "[Q*cert] "
	@$(MAKE) -C javaService install
endif

clean-coq:
	@$(MAKE) -f Makefile.coq clean

cleanall-coq: clean-coq

clean-ocaml:
	@$(MAKE) -C ocaml clean

cleanall-ocaml:
	@$(MAKE) -C ocaml cleanall

clean-java:
	@$(MAKE) -C javaService clean
	@$(MAKE) -C sqlParser clean
	@$(MAKE) -C sqlppParser clean
	@$(MAKE) -C camp-java clean
	@$(MAKE) -C jrules2CAMP clean
	@rm -rf bin/services
	@rm -f bin/javaService.jar

cleanall-java:
	@$(MAKE) -C javaService cleanall
	@$(MAKE) -C sqlParser cleanall
	@$(MAKE) -C sqlppParser cleanall
	@$(MAKE) -C camp-java cleanall
	@$(MAKE) -C jrules2CAMP cleanall
	@rm -rf bin/services
	@rm -f bin/javaService.jar


## Runtime
qcert-runtimes:
	@$(MAKE) javascript-runtime
ifneq ($(JAVA),)
	@$(MAKE) java-runtime
endif
ifneq ($(SPARK),)
	@$(MAKE) spark2-runtime
endif

javascript-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building JavaScript runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtime/javascript

java-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Java runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtime/java

spark2-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Spark2 runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtime/spark2

clean-runtimes:
	@$(MAKE) -C runtime/javascript clean
	@$(MAKE) -C runtime/java clean
	@$(MAKE) -C runtime/spark2 clean

cleanall-runtimes:
	@$(MAKE) -C runtime/javascript cleanall
	@$(MAKE) -C runtime/java cleanall
	@$(MAKE) -C runtime/spark2 cleanall


## Demo
demo: bin/qcertJS.js
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling TypeScript files to JavaScript"
	@echo "[Q*cert] "
	cd webdemo && $(TSC) -p "tsconfig.json"


## Runners
qcert-runners:
	@$(MAKE) -C samples

clean-runners:
	@$(MAKE) -C samples clean

cleanall-runners:
	@$(MAKE) -C samples cleanall

## Documentation
documentation:
	$(MAKE) -C coq documentation


## Cleanup
clean: Makefile.coq remove_all_derived
	@$(MAKE) clean-coq
	@$(MAKE) clean-ocaml
	@$(MAKE) clean-java
	@$(MAKE) clean-runtimes
	@$(MAKE) clean-runners
	@rm -f Makefile.coq
	@rm -f *~

cleanall: Makefile.coq remove_all_derived
	@$(MAKE) cleanall-coq
	@$(MAKE) cleanall-ocaml
	@$(MAKE) cleanall-java
	@$(MAKE) cleanall-runtimes
	@$(MAKE) cleanall-runners
	@rm -f Makefile.coq
	@rm -f *~

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 ./script/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

##
Makefile.coq: Makefile $(VS) $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean clean_detritus documentation documentation_old

