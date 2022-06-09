/*
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

export as namespace Qcert;

export type Language = string;

export type LanguageDescription = {langid:Language, label:string, description:string};
export type SourceLanguageGroups = {
		frontend:[LanguageDescription], 
		core:[LanguageDescription], 
		distributed:[LanguageDescription], 
		backend:[LanguageDescription]};

export type OptimStepDescription = {name: string, description:string, lemma:string};

export type OptimPhase = {name: string; optims: {[key: string]: string[]}; iter: number};
export type OptimConfig = {language: string; phases: OptimPhase[]};

export type ConfigObject = {};

export type CompilerConfig = {
    source:Language, /* Source language */
    target:Language, /* Target language */
    path:string[],        /* Intermediate compilation steps (excluding source/target) */
    exactpath: boolean,   /* true if forcing exact compilation path */
    emitall: boolean      /* true if emitting for all intermediate languages */
    sourcesexp: boolean,  /* true if input language uses s-expression syntax */
    ascii: boolean,       /* true for ascii pp instead of greek pp */
    javaimports: string,  /* optional java imports for Java back-end */
    schema: string,       /* the schema */
    input: string,        /* the (JSON format) input data) */
    eval: boolean,        /* True if evaluation is to be conducted on the target language */
    optims: string };     /* Optimizations configuration */

export type ResultFile = {
    file: string;         /* File name */
    lang: string;         /* Language name */
    value: string};       /* Emitted code */

export type Result = {
    emit: ResultFile;
    emitall: ResultFile[];
    result: string,
    eval: string};

/**  Returns the set of languages known by the compiler, grouped into phases */
export declare function languages(): SourceLanguageGroups;

/**
 * Derives a default path between the arguments
 * @param args Specifies the source and target languages
 * @returns Includes the source and target languages in the returned path.
 * If no path was found, an array with a single element "error" will be returned.
 */
export declare function languagesPath(args:{source:Language, target:Language}): {path: Language[]};

export declare function optimList():{optims:{language:{name:Language, modulebase:string}, optims:{[key: string]: OptimStepDescription[]}}[]};

/** Returns the set of default optimization phases and rewrites for each language */
export declare function optimDefaults(): {optims: OptimConfig[]};

export declare function buildConfig(conf:CompilerConfig): ConfigObject;

/** Main compilation call
 * @config specifies the compilation parameters, including source,target,ascii/greek,additional java imports, and the query in source form
 * @returns Includes the intermediate representation for the target language
 */
export declare function compile(config:{ query: string, gconf: ConfigObject }): Result;

