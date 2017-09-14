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
package testing.runners;

/** Provides mapping from dbCopy back to viewName+defaultExpr
 */
public class CloudantOut {

	String _dbName;
	String _viewName;
	String _defaultExpr;
        String _dbCopyName;

        CloudantOut() {
	    _dbName=null;
	    _viewName=null;
	    _defaultExpr=null;
	    _dbCopyName=null;
        }
    
        CloudantOut(String dbName, String viewName, String defaultExpr, String dbCopyName) {
		_dbName = dbName;
		_viewName = viewName;
		_defaultExpr = defaultExpr;
		_dbCopyName = dbCopyName;
	}
	
	// Return dbName
	public String getDbName() {
		return _dbName;
	}
	
	// Return viewName
	public String getViewName() {
		return _viewName;
	}
	
	// Return defaultExpr
	public String getDefaultExpr() {
		return _defaultExpr;
	}
	
	// Return dbCopyName
	public String getDbCopyName() {
		return _dbCopyName;
	}

        // Add viewName
        public void addViewName(String viewName) {
	    _viewName = viewName;
	}
    
	// Convert to string
	public String toString() {
	    return "dbCopy [" + _dbCopyName +  "] is mapped to view : [" + _viewName + "] from database [" + _dbName + "]";
	}
	
}
