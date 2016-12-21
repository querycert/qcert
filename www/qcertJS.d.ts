type QcertLanguage = string;

type SourceLanguageGroups = {
		frontend:[{langid:QcertLanguage, label:string}], 
		intermediate:[{langid:QcertLanguage, label:string}], 
		backend:[{langid:QcertLanguage, label:string}]};

/**  Returns the set of languages known by the compiler, grouped into phases */
declare function qcertLanguages(): SourceLanguageGroups;

/**
 * Derives a default path between the arguments
 * @param args Specifies the source and target languages
 * @returns Includes the source and target languages in the returned path.
 * If no path was found, an array with a single element "error" will be returned.
 */
declare function qcertLanguagesPath(args:{source:QcertLanguage, target:QcertLanguage}): {path: QcertLanguage[]}