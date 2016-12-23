type QcertLanguage = string;

type QcertLanguageDescription = {langid:QcertLanguage, label:string, description:string};
type SourceLanguageGroups = {
		frontend:[QcertLanguageDescription], 
		intermediate:[QcertLanguageDescription], 
		backend:[QcertLanguageDescription]};

type QcertOptimPhase = {name: string; optims: string[]; iter: number};
type QcertOptimConfig = {language: string; phases: QcertOptimPhase[]};
type QcertCompilerConfig = {source:QcertLanguage, target:QcertLanguage, sourcesexp: boolean, ascii: boolean, javaimports: string, query: string};

/**  Returns the set of languages known by the compiler, grouped into phases */
declare function qcertLanguages(): SourceLanguageGroups;

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
declare function qcertCompile(config:QcertCompilerConfig): string;

