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

/* Import ASTs */
import org.qcert.calib.CALibWrapper.camp;
import org.qcert.calib.CALibWrapper.nraenv;
import org.qcert.calib.CALibWrapper.nnrc;
import org.qcert.calib.CALibWrapper.nnrcmr;
import org.qcert.calib.CALibWrapper.cldmr;

public interface CACoEngineAPI {

    /*
     *  Frontend section
     */

    /* From source to CAMP */
    camp rule_to_camp(String rule);

    /* From camp to NRAEnv */
    nraenv camp_to_nraenv(camp c);

    /* From source to NRAEnv */
    nraenv rule_to_nraenv(String rule);
    nraenv oql_to_nraenv(String oql);

    /*
     *  Core compiler section
     */

    /* Translations */
    nnrc translate_nraenv_to_nnrc(nraenv n);
    nnrcmr translate_nnrc_to_nnrcmr(nnrc n);

    /* NRAEnv Optimizer */
    nraenv optimize_nraenv(nraenv n);

    /* NNRC Optimizer */
    nnrc optimize_nnrc(nnrc n);

    /* NNRCMR Optimizer */
    nnrcmr optimize_nnrcmr(nnrcmr n);
    nnrcmr optimize_nnrcmr_for_cloudant(nnrcmr n);
    nnrcmr optimize_nnrcmr_for_spark(nnrcmr n);

    /* For convenience */
    /* Note: This includes optimization phases */
    nnrc compile_nraenv_to_nnrc(nraenv n);
    nnrcmr compile_nraenv_to_nnrcmr(nraenv n);


    /*
     *  Backend section
     */

    String nnrc_to_js(nnrc n);
    String nnrc_to_java(String basename, String imports, nnrc n);
    String nnrcmr_to_spark(String nrule, nnrcmr n);

    cldmr translate_nnrcmr_to_cldmr(nnrcmr n);

    String cldmr_to_cloudant(String harness, String prefix, String nrule, cldmr n);

    /* For convenience */
    String nraenv_to_js(nraenv n);
    String nraenv_to_java(String basename, String imports, nraenv n);
    String nraenv_to_spark(String nrule, nraenv n);
    String nraenv_to_cloudant(String harness, String prefix, String nrule, nraenv n);
    String nnrcmr_to_cloudant(String harness, String prefix, String nrule, nnrcmr n);

    /*
     *  ASTs support
     */

    /* Import/Export ASTs */
    String export_camp(camp n);
    camp import_camp(String ns);

    String export_nraenv(nraenv n);
    nraenv import_nraenv(String ns);

    String export_nnrc(nnrc n);
    nnrc import_nnrc(String ns);

    String export_nnrcmr(nnrcmr n);
    nnrcmr import_nnrcmr(String ns);

    String export_cldmr(cldmr n);
    cldmr import_cldmr(String ns);

    /* Pretties */
    String pretty_nraenv(boolean greek, long margin, nraenv n);
    String pretty_nnrc(boolean greek, long margin, nnrc n);
    String pretty_nnrcmr_for_spark(boolean greek, long margin, nnrcmr nmr);
    String pretty_nnrcmr_for_cloudant(boolean greek, long margin, nnrcmr nmr);

    /* Options */

    void set_optim_trace();
    void unset_optim_trace();

}
