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
	Basic/Data/RBag \
	Basic/Data/RDomain \
	Basic/Data/BrandRelation \
	Basic/Data/ForeignData \
	Basic/Data/RData \
	Basic/Data/RDataNorm \
	Basic/Data/RRelation \
	Basic/Data/RGroupBy \
	Basic/Data/LData \
	Basic/Data/DData \
	Basic/Data/DDataNorm \
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
	NRA/Optim/ROptim \
	NRA/Optim/ROptimContext \
	NRA/Optim/ROptimExt \
	NRA/Optim/TOptim \
	NRA/NRARuntime \
	NRA/NRATypes \
	NRA/NRASystem \
	NRAEnv/Algebra/RAlgEnv \
	NRAEnv/Algebra/RAlgEnvSize \
	NRAEnv/Algebra/RAlgEnvIgnore \
	NRAEnv/Algebra/RAlgEnvEq \
        NRAEnv/Algebra/RAlgEnvExt \
        NRAEnv/Algebra/RAlgEnvExtEq \
	NRAEnv/Typing/TAlgEnv \
	NRAEnv/Typing/TAlgEnvInfer \
	NRAEnv/Typing/TAlgEnvIgnore \
        NRAEnv/Typing/TAlgEnvEq \
	NRAEnv/Typing/TAlgEnvExt \
	NRAEnv/Context/RAlgEnvContext \
	NRAEnv/Context/RAlgEnvContextLift \
	NRAEnv/Optim/ROptimEnv \
	NRAEnv/Optim/ROptimEnvContext \
	NRAEnv/Optim/TOptimEnv \
	NRAEnv/NRAEnvRuntime \
	NRAEnv/NRAEnvTypes \
	NRAEnv/NRAEnvSystem \
	NNRC/Calculus/NNRC \
	NNRC/Calculus/ForeignReduceOps \
	NNRC/Calculus/NNRCEq \
	NNRC/Calculus/NNRCSize \
	NNRC/Calculus/NShadow \
	NNRC/Calculus/NNRCMR \
	NNRC/Typing/TNRC \
	NNRC/Typing/TNRCInfer \
	NNRC/Typing/TNRCEq \
	NNRC/Typing/TShadow \
	NNRC/Rew/NRewUtil \
	NNRC/Rew/NRew \
	NNRC/Rew/NRewMR \
	NNRC/Rew/TRew \
	NNRC/NNRCRuntime \
	NNRC/NNRCTypes \
	NNRC/NNRCSystem \
	NNRC/NNRCMRRuntime \
	DNNRC/Calculus/DNNRC \
	DNNRC/Calculus/DNNRCEq \
	DNNRC/Calculus/SparkIR \
	DNNRC/Typing/TDNNRC \
	CAMP/Rules/Pattern \
	CAMP/Rules/PatternSize \
	CAMP/Rules/PatternSugar \
	CAMP/Rules/Rule \
	CAMP/Rules/RuleSugar \
	CAMP/Typing/TPattern \
	CAMP/Typing/TPatternSugar \
	CAMP/Typing/TRule \
	CAMP/CAMPRuntime \
	CAMP/CAMPTypes \
	CAMP/CAMPSystem \
	Translation/ForeignToReduceOps \
	Translation/NRAtoNNRC \
	Translation/NRAEnvtoNNRC \
	Translation/NNRCtoPattern \
	Translation/NNRCtoNNRCMR \
	Translation/NNRCMRtoNNRC \
	Translation/PatterntoNRA \
	Translation/PatterntoNRAEnv \
	Translation/PatternSugartoNRA \
	Translation/RuletoNRA \
	Translation/RuletoNRAEnv \
	Translation/TNRAtoNNRC \
	Translation/TNRAEnvtoNNRC \
	Translation/TNNRCtoPattern \
	Translation/TPatterntoNRA \
	Translation/TPatterntoNRAEnv \
	Frontend/ODMG/OQL \
	Frontend/ODMG/OQLSugar \
	Frontend/ODMG/OQLSize \
	Frontend/ODMG/OQLtoNRAEnv \
	Frontend/ODMGRuntime \
	Backend/ForeignToJSON \
	Backend/ForeignCloudant \
	Backend/ForeignToJava \
	Backend/ForeignToJavascript \
	Backend/CloudantKV \
	Backend/CloudantMR \
	Backend/ForeignToCloudant \
	Backend/ForeignToSpark \
	Backend/JSON \
	Backend/NNRCtoJava \
	Backend/NNRCtoJavascript \
	Backend/NNRCMRtoSpark \
	Backend/NNRCMRtoCloudant \
	Backend/CloudantMRtoJavascript \
	Backend/DNNRCtoScala \
	Compiler/Optimizer/OptimizerLogger \
	Compiler/Optimizer/ROptimEnvFunc \
	Compiler/Optimizer/TOptimEnvFunc \
	Compiler/Optimizer/NRewFunc \
	Compiler/Optimizer/TRewFunc \
	Compiler/CompilerModel/CompilerRuntime \
	Compiler/Top/CompData \
	Compiler/Top/CompOperators \
	Compiler/Top/CompPattern \
	Compiler/Top/CompRule \
	Compiler/Top/CompOQL \
	Compiler/Top/CompUtil \
	Compiler/Top/CompFront \
	Compiler/Top/CompCore \
	Compiler/Top/CompBack \
	Compiler/Top/CompTop \
	Compiler/Top/EvalTop \
	Compiler/Top/OQLTop \
	Compiler/CompilerModel/CompilerModel \
	Compiler/Top/CompCorrect \
	Compiler/Top/CompStat \
	Compiler/Top/CompType \
	Compiler/CompilerModel/FloatModelPart \
	Compiler/CompilerModel/StringModelPart \
	Compiler/CompilerModel/DateTimeModelPart \
	Compiler/CompilerModel/EnhancedModel \
	Compiler/CompilerModel/TrivialModel \
	Tests/PatternTest \
	Compiler/Compiler \
	Compiler/EnhancedCompiler \
	Compiler/TrivialCompiler \
	Tests/RAlgTest \
	Tests/TAlgTest \
	Tests/BrandTest \
	Tests/TBrandTest \
	Tests/CompilerTest \
	Tests/MRTest \
	Tests/OQLTest

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

qcert: Makefile.coq
	@echo "[QCert] "
	@echo "[QCert] Compiling Coq source"
	@echo "[QCert] "
	@$(MAKE) -f Makefile.coq

extraction:
	@echo "[QCert] "
	@echo "[QCert] Extracting compiler to OCaml"
	@echo "[QCert] "
	@$(MAKE) -C ocaml realclean all

java-extraction:
	@echo "[QCert] "
	@echo "[QCert] Extracting compiler to OCaml + Java"
	@echo "[QCert] "
	@$(MAKE) -C ocaml clean japi

Makefile.coq: Makefile $(VS) $(FILES)
	@coq_makefile -R coq QCert $(FILES) -o Makefile.coq

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

