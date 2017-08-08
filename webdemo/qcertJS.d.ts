type QcertLanguage = string;

type QcertLanguageDescription = {langid:QcertLanguage, label:string, description:string};
type SourceLanguageGroups = {
		frontend:[QcertLanguageDescription], 
		core:[QcertLanguageDescription], 
		distributed:[QcertLanguageDescription], 
		backend:[QcertLanguageDescription]};

type QcertOptimStepDescription = {name: string, description:string, lemma:string};

type QcertOptimPhase = {name: string; optims: string[]; iter: number};
type QcertOptimConfig = {language: string; phases: QcertOptimPhase[]};
type QcertCompilerConfig = {
    source:QcertLanguage, /* Source language */
    target:QcertLanguage, /* Target language */
    path:string[],        /* Intermediate compilation steps (excluding source/target) */
    exactpath: boolean,   /* true if forcing exact compilation path */
    emitall: boolean      /* true if emitting for all intermediate languages */
    sourcesexp: boolean,  /* true if input language uses s-expression syntax */
    ascii: boolean,       /* true for ascii pp instead of greek pp */
    javaimports: string,  /* optional java imports for Java back-end */
    query: string,        /* Input query */
    schema: string,       /* the schema */
    input: string,        /* the (JSON format) input data) */
    eval: boolean,        /* True if evaluation is to be conducted on the target language */
    optims: string };     /* Optimizations configuration */

type QcertResultFile = {
    file: string;         /* File name */
    lang: string;         /* Language name */
    value: string};       /* Emitted code */

type QcertResult = {
    emit: QcertResultFile;
    emitall: QcertResultFile[];
    result: string,
    eval: string};

/**  Returns the set of languages known by the compiler, grouped into phases */
declare function qcertLanguages(): SourceLanguageGroups;

declare function qcertOptimList():{optims:{language:{name:QcertLanguage, modulebase:string}, optims:QcertOptimStepDescription[]}[]};

/**
 * Derives a default path between the arguments
 * @param args Specifies the source and target languages
 * @returns Includes the source and target languages in the returned path.
 * If no path was found, an array with a single element "error" will be returned.
 */
declare function qcertLanguagesPath(args:{source:QcertLanguage, target:QcertLanguage}): {path: QcertLanguage[]};

/** Returns the set of default optimization phases and rewrites for each language */
declare function qcertOptimDefaults(): {optims: QcertOptimConfig[]};

/** Main compilation call
 * @config specifies the compilation parameters, including source,target,ascii/greek,additional java imports, and the query in source form
 * @returns Includes the intermediate representation for the target language
 */
declare function qcertCompile(config:QcertCompilerConfig): QcertResult;

