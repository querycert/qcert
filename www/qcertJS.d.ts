type QcertLanguage = string;

type QcertLanguageDescription = {langid:QcertLanguage, label:string, description:string};
type SourceLanguageGroups = {
		frontend:[QcertLanguageDescription], 
		intermediate:[QcertLanguageDescription], 
		backend:[QcertLanguageDescription]};

/**  Returns the set of languages known by the compiler, grouped into phases */
declare function qcertLanguages(): SourceLanguageGroups;

/**
 * Derives a default path between the arguments
 * @param args Specifies the source and target languages
 * @returns Includes the source and target languages in the returned path.
 * If no path was found, an array with a single element "error" will be returned.
 */
declare function qcertLanguagesPath(args:{source:QcertLanguage, target:QcertLanguage}): {path: QcertLanguage[]}