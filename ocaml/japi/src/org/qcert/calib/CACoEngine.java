/*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.qcert.calib;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

/* Import ASTs */
import org.qcert.calib.CALibWrapper;
import org.qcert.calib.CALibWrapper.camp;
import org.qcert.calib.CALibWrapper.nraenv;
import org.qcert.calib.CALibWrapper.nnrc;
import org.qcert.calib.CALibWrapper.nnrcmr;
import org.qcert.calib.CALibWrapper.cldmr;

public class CACoEngine implements CACoEngineAPI {

    static {
	/* ocamlJava runtime should be initialized before anything else can happen */
	ocamljavaMain.mainWithReturn(new String[0]);
    }

    /* From source to CAMP */
    public camp rule_to_camp(String rule) {
	return CALibWrapper.rule_to_camp(rule);
    }
 
    /* From camp to NRAEnv */
    public nraenv camp_to_nraenv(camp c) {
	return CALibWrapper.camp_to_nraenv(c);
    }

    /* From source to NRAEnv */
    public nraenv rule_to_nraenv(String rule) {
	return CALibWrapper.rule_to_nraenv(rule);
    }
    public nraenv oql_to_nraenv(String oql) {
	return CALibWrapper.oql_to_nraenv(oql);
    }

    /*
     *  Core compiler section
     */

    /* Translations */
    public nnrc translate_nraenv_to_nnrc(nraenv op) {
	return CALibWrapper.translate_nraenv_to_nnrc(op);
    }
    public nnrcmr translate_nnrc_to_nnrcmr(nnrc n) {
	return CALibWrapper.translate_nnrc_to_nnrcmr(n);
    }

    /* NRAEnv Optimizer */
    public nraenv optimize_nraenv(nraenv op) {
	return CALibWrapper.optimize_nraenv(op);
    }

    /* NNRC Optimizer */
    public nnrc optimize_nnrc(nnrc n) {
	return CALibWrapper.optimize_nnrc(n);
    }

    /* NNRCMR Optimizer */
    public nnrcmr optimize_nnrcmr(nnrcmr n) {
	return CALibWrapper.optimize_nnrcmr(n);
    }

    public nnrcmr optimize_nnrcmr_for_cloudant(nnrcmr n) {
	return CALibWrapper.optimize_nnrcmr_for_cloudant(n);
    }

    public nnrcmr optimize_nnrcmr_for_spark(nnrcmr n) {
	return CALibWrapper.optimize_nnrcmr_for_spark(n);
    }

    /* For convenience */
    /* Note: This includes optimization phases */
    public nnrc compile_nraenv_to_nnrc(nraenv n) {
	return CALibWrapper.compile_nraenv_to_nnrc(n);
    }
    public nnrcmr compile_nraenv_to_nnrcmr(nraenv n) {
	return CALibWrapper.compile_nraenv_to_nnrcmr(n);
    }

    /*
     *  Backend section
     */

    public String nnrc_to_js(nnrc n) {
	return CALibWrapper.nnrc_to_js(n);
    }
    public String nnrc_to_java(String basename, String imports, nnrc n) {
	return CALibWrapper.nnrc_to_java(basename, imports, n);
    }
    public String nnrcmr_to_spark(String nrule, nnrcmr n) {
	return CALibWrapper.nnrcmr_to_spark(nrule,n);
    }

    public cldmr translate_nnrcmr_to_cldmr(nnrcmr n) {
	return CALibWrapper.translate_nnrcmr_to_cldmr(n);
    };

    public String cldmr_to_cloudant(String harness, String prefix, String nrule, cldmr n) {
	String inline_harness = (harness.replace("\t", " ")).replace("\"","\\\""); /* replacing \t is safer since Cloudant doesn't like tabs */
	String designdocs = CALibWrapper.cldmr_to_cloudant(prefix,nrule,n);
	String designdocs_harnessed = designdocs.replace("%HARNESS%", inline_harness);
	return designdocs_harnessed;
    };

    /* For convenience */
    /* From NRAEnv to Backend */
    public String nraenv_to_js(nraenv n) {
	return CALibWrapper.compile_nraenv_to_js(n);
    }
    public String nraenv_to_java(String basename, String imports, nraenv n) {
	return CALibWrapper.compile_nraenv_to_java(basename, imports, n);
    }
    public String nraenv_to_cloudant(String harness, String prefix, String nrule, nraenv n) {
	String inline_harness = (harness.replace("\t", " ")).replace("\"","\\\""); /* replacing \t is safer since Cloudant doesn't like tabs */
	String designdocs = CALibWrapper.compile_nraenv_to_cloudant(prefix,nrule,n);
	String designdocs_harnessed = designdocs.replace("%HARNESS%", inline_harness);
	return designdocs_harnessed;
    }
    public String nraenv_to_spark(String nrule, nraenv n) {
	return CALibWrapper.compile_nraenv_to_spark(nrule,n);
    }
    public String nnrcmr_to_cloudant(String harness, String prefix, String nrule, nnrcmr n) {
	String inline_harness = (harness.replace("\t", " ")).replace("\"","\\\""); /* replacing \t is safer since Cloudant doesn't like tabs */
	String designdocs = CALibWrapper.compile_nnrcmr_to_cloudant(prefix,nrule,n);
	String designdocs_harnessed = designdocs.replace("%HARNESS%", inline_harness);
	return designdocs_harnessed;
    };

    /*
     *  ASTs support
     */

    /* Import/Export ASTs */

    public String export_camp(camp p) {
	return CALibWrapper.export_camp(p);
    }
    public camp import_camp(String ps) {
	return CALibWrapper.import_camp(ps);
    }

    public String export_nraenv(nraenv n) {
	return CALibWrapper.export_nraenv(n);
    }
    public nraenv import_nraenv(String ns) {
	return CALibWrapper.import_nraenv(ns);
    }

    public String export_nnrc(nnrc n) {
	return CALibWrapper.export_nnrc(n);
    }
    public nnrc import_nnrc(String ns) {
	return CALibWrapper.import_nnrc(ns);
    }

    public String export_nnrcmr(nnrcmr n) {
	return CALibWrapper.export_nnrcmr(n);
    }
    public nnrcmr import_nnrcmr(String ns) {
	return CALibWrapper.import_nnrcmr(ns);
    }

    public String export_cldmr(cldmr n) {
	return CALibWrapper.export_cldmr(n);
    }
    public cldmr import_cldmr(String ns) {
	return CALibWrapper.import_cldmr(ns);
    }

    /* Pretties */
    public String pretty_nraenv(boolean greek, long margin, nraenv n) {
	return CALibWrapper.pretty_nraenv(greek,margin,n);
    }
    public String pretty_nnrc(boolean greek, long margin, nnrc n) {
	return CALibWrapper.pretty_nnrc(greek,margin,n);
    }
    public String pretty_nnrcmr_for_spark(boolean greek, long margin, nnrcmr nmr) {
	return CALibWrapper.pretty_nnrcmr_for_spark(greek,margin,nmr);
    }
    public String pretty_nnrcmr_for_cloudant(boolean greek, long margin, nnrcmr nmr) {
	return CALibWrapper.pretty_nnrcmr_for_cloudant(greek,margin,nmr);
    }

    /* Options */

    public void set_optim_trace() { CALibWrapper.set_optim_trace(); }
    public void unset_optim_trace() { CALibWrapper.unset_optim_trace(); }

}
