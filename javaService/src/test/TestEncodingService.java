/**
 * Copyright (C) 2016 Joshua Auerbach 
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
package test;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.HttpStatus;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.entity.FileEntity;
import org.apache.http.impl.client.HttpClients;

/**
 * Just a test that we are able to communicate with the Java service at localhost or AWS instance, port 9879.
 * Currently just tests the SQL parser.
 */
public class TestEncodingService {
	public static void main(String[] args) throws Exception {
		String file, url;
		if (args.length == 2 && args[0].equals("remote")) {
			file = args[1];
			url = "http://35.164.159.76:9879?verb=parseSQL";
		} else if (args.length == 1) {
			file = args[0];
			url = "http://localhost:9879?verb=parseSQL";
		} else {
			System.out.println("Wrong number of arguments");
			return;
		}
		FileEntity entity = new FileEntity(new File(file));
		HttpClient client = HttpClients.createDefault();
		HttpPost post = new HttpPost(url);
		entity.setContentType("text/plain");
		post.setEntity(entity);
		HttpResponse resp = client.execute(post);
		int code = resp.getStatusLine().getStatusCode();
		if (code == HttpStatus.SC_OK) {
			HttpEntity answer = resp.getEntity();
			InputStream s = answer.getContent();
			BufferedReader rdr = new BufferedReader(new InputStreamReader(s));
			String line = rdr.readLine();
			while (line != null) {
				System.out.println(line);
				line = rdr.readLine();
			}
			rdr.close();
			s.close();
		} else
			System.out.println(resp.getStatusLine());
	}
}
