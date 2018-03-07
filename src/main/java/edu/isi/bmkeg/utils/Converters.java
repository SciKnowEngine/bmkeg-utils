package edu.isi.bmkeg.utils;

import java.awt.image.BufferedImage;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.StringReader;
import java.net.URI;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.Adler32;
import java.util.zip.CheckedInputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import static org.apache.commons.text.CharacterPredicates.DIGITS;
import static org.apache.commons.text.CharacterPredicates.LETTERS;
import org.apache.commons.text.RandomStringGenerator;
import org.w3c.dom.Document;
import org.w3c.dom.bootstrap.DOMImplementationRegistry;
import org.w3c.dom.ls.DOMImplementationLS;
import org.w3c.dom.ls.LSSerializer;
import org.xml.sax.InputSource;

public class Converters {

	private static Logger log = Logger
			.getLogger("edu.isi.bmkeg.utils.Converters");

	private static int HTML_TEXT_SIZE = 4;
	private static int BUFFER = 2048;

	public static String classpathToUri(String classpath) {

		String uri = "";

		if (classpath.indexOf("/") != -1
				&& classpath.indexOf("/") == classpath.lastIndexOf("/")) {
			return classpath;
		}

		//
		// This is the path to the top level category...
		// This will be of the format 'edu.usc.kmrg.coresystem'
		// (which we need to transform to 'kmrg.usc.edu/coreSystem')
		//
		String[] cats = classpath.split("\\.");

		//
		// Count down from the last but one entry in the topPath
		//
		for (int i = cats.length - 2; i >= 0; i--) {
			if (uri.length() > 0) {
				uri += ".";
			}
			uri += cats[i];
		}
		uri += "/" + cats[cats.length - 1];

		return uri;

	}

	public static String uriToClasspath(String uri) {

		String cp = "";

		if (uri.indexOf("/") == -1 && uri.indexOf("/") != uri.lastIndexOf("/")) {
			return cp;
		}

		//
		// The Uri has the form 'path.to.site/classname'
		// We want to change this to 'site.to.path.classname')
		//
		String[] beforeAfter = uri.split("\\/");
		if (beforeAfter.length != 2) {
			return cp;
		}

		String stem = beforeAfter[0];
		String[] cats = stem.split("\\.");
		for (int i = cats.length - 1; i >= 0; i--) {
			if (cp.length() > 0) {
				cp += ".";
			}
			cp += cats[i];
		}
		cp += "." + beforeAfter[1];

		return cp;

	}

	/**
	 * A function to track memory usage
	 */
	public static void printMemory(boolean stack) {

		if (stack) {
			System.out.println("Current memory and position");

			Exception e = new Exception("current stack");
			StackTraceElement[] stea = e.getStackTrace();
			for (int i = 1; i < stea.length; i++) {

				System.out.println("    " + stea[i].getClassName() + "."
						+ stea[i].getMethodName() + "(), "
						+ stea[i].getFileName() + ":" + stea[i].getLineNumber()
						+ ";");
			}
		}

		String t = "" + (Runtime.getRuntime().totalMemory() / 1000000.0);
		int tl = t.indexOf(".");
		String m = "" + (Runtime.getRuntime().maxMemory() / 1000000.0);
		int ml = m.indexOf(".");
		String f = "" + (Runtime.getRuntime().freeMemory() / 1000000.0);
		int fl = f.indexOf(".");

		System.out.println(f.substring(0, fl + 2) + "/"
				+ t.substring(0, tl + 2) + "(" + m.substring(0, ml + 2) + ")");

	}

	public static byte[] fileContentsToBytesArray(File file) throws IOException {

		InputStream is = new FileInputStream(file);

		// Get the size of the file
		long length = file.length();

		// You cannot create an array using a long type.
		// It needs to be an int type.
		// Before converting to an int type, check
		// to ensure that file is not larger than Integer.MAX_VALUE.
		if (length > Integer.MAX_VALUE) {
			// File is too large
		}

		// Create the byte array to hold the data
		byte[] bytes = new byte[(int) length];

		// Read in the bytes
		int offset = 0;
		int numRead = 0;
		while (offset < bytes.length
				&& (numRead = is.read(bytes, offset, bytes.length - offset)) >= 0) {
			offset += numRead;
		}

		// Ensure all the bytes have been read in
		if (offset < bytes.length) {
			throw new IOException("Could not completely read file "
					+ file.getName());
		}

		// Close the input stream and return bytes
		is.close();
		return bytes;
	}

	public static File extractFileFromJarClasspath(String localDir, String classPath) throws IOException {
		
		InputStream is = Converters.class.getClassLoader().getResourceAsStream(classPath);
		if(is == null)
			return null;
		
		String fileName = classPath.substring(classPath.lastIndexOf("/")+1, classPath.length());
		File file = new File( localDir + "/" + fileName ); 
		OutputStream out = new FileOutputStream(file);
		int read = 0;
		byte[] bytes = new byte[1024];
		while ((read = is.read(bytes)) != -1) {
			out.write(bytes, 0, read);
		}
		is.close();
		out.flush();
		out.close();
		
		return file;
		
	}	
	
	public static void jarIt(Map<String, File> filesToZip, File targetZip)
			throws Exception {

		// Create a buffer for reading the files
		byte[] buf = new byte[1024];

		// Create the ZIP file
		Manifest manifest = new Manifest();
		manifest.getMainAttributes().put(Attributes.Name.MANIFEST_VERSION,
				"1.0");
		JarOutputStream out = new JarOutputStream(new FileOutputStream(
				targetZip), manifest);

		// Compress the files
		Iterator<String> keyIt = filesToZip.keySet().iterator();
		while (keyIt.hasNext()) {
			String key = keyIt.next();
			File f = filesToZip.get(key);

			FileInputStream in = new FileInputStream(f);

			// Add ZIP entry to output stream.
			out.putNextEntry(new JarEntry(key));

			// Transfer bytes from the file to the ZIP file
			int len;
			while ((len = in.read(buf)) > 0) {
				out.write(buf, 0, len);
			}

			// Complete the entry
			out.closeEntry();
			in.close();
		}

		// Complete the ZIP file
		out.close();

	}

	/**
	 * BE BLOODY CAREFUL WHEN USING THIS.
	 * 
	 * @param dir
	 * @throws Exception
	 */
	public static void recursivelyDeleteFiles(File dir)  {

		log.info("DELETING FILES FROM " + dir.getPath());

		Map<String, File> toDelete = Converters.recursivelyListFiles(dir,
				new HashMap<String, File>());
		Converters.cleanItUp(toDelete);

		if (dir.exists()) {
			log.info("FAILED");
		} else {
			log.info("SUCCESS");
		}

	}

	/**
	 * BE BLOODY CAREFUL WHEN USING THIS.
	 * 
	 * @param dir
	 * @throws Exception
	 */
	public static void cleanContentsFiles(File dir, String suffixToLeave)
			throws Exception {

		log.info("DELETING FILES FROM " + dir.getPath());

		Map<String, File> toDelete = Converters.recursivelyListFiles(dir,
				new HashMap<String, File>());

		toDelete.remove(dir.getPath());
		List<String> keys = new ArrayList<String>(toDelete.keySet());
		Iterator<String> it = keys.iterator();
		while (it.hasNext()) {
			String path = it.next();
			if (path.endsWith("." + suffixToLeave))
				toDelete.remove(path);
		}

		Converters.cleanItUp(toDelete);

	}

	public static Map<String, File> recursivelyListFiles(File dir) throws Exception {
		return recursivelyListFiles(dir, new HashMap<String, File>());
	}
	
	public static Map<String, File> recursivelyListFiles(File dir,
			Map<String, File> m) {
		
		m.put(dir.getPath(), dir);
		File[] fArray = dir.listFiles();
		
		if( fArray == null ) 
			return m;
		
		for (int i = 0; i < fArray.length; i++) {
			File f = fArray[i];
			if (fArray[i].isDirectory()) {
				m.putAll(Converters.recursivelyListFiles(f, m));
			}
			m.put(f.getPath(), f);
		}
		return m;
	}
	
	public static Map<String, File> recursivelyListFiles(File dir, Pattern patt) throws Exception {
		return recursivelyListFiles(dir, new HashMap<String, File>(), patt);
	}
	

	public static Map<String, File> recursivelyListFiles(File dir,
			Map<String, File> m, Pattern patt) throws Exception {

		Matcher match = patt.matcher(dir.getName());
		if (match.find())
			m.put(dir.getPath(), dir);

		File[] fArray = dir.listFiles();
		for (int i = 0; i < fArray.length; i++) {
			File f = fArray[i];

			if (fArray[i].isDirectory()) {
				m.putAll(Converters.recursivelyListFiles(f, m, patt));
			}
			
			match = patt.matcher(f.getName());
			if (match.find())
				m.put(f.getPath(), f);

		}

		return m;

	}
	
	/**
	 * This will generate a mimicked subdirectory structure for an input file 
	 * relative to a stem for a new output stem. i.e., Mimicking the file
	 * /files/data/1/2/3/xyz.txt based on the stem /files to the new output 
	 * stem /files2 will return the file /files2/data/1/2/3/xyz.txt (with all
	 * the intermediate directories automatically generated). 
	 * 
	 * @param inStem
	 * @param outStem
	 * @param in
	 * @return
	 */
	public static File mimicDirectoryStructure( File inStem, File outStem, File in) {
		
		String filler = in.getPath().replaceAll(inStem.getPath(), "");
		String newPath = outStem.getPath() + "/" + filler;
		File out = new File( newPath );
		
		// Make sure we reproduce the same 
		// directory structure in the 
		// output as we have in the input.
		File dir = out.getParentFile();
		List<File> dirsToMake = new ArrayList<File>();
		while( !dir.exists() ) {
			dirsToMake.add(dir);
			dir = dir.getParentFile();
		}
		for(int i=dirsToMake.size()-1; i>=0; i--) {
			File dirToMake = dirsToMake.get(i);
			dirToMake.mkdir();
		}
	
		return out;
		
	}

	public static Map<String, File> zipPrep(String stem, File dir,
			Map<String, File> filesToZip) throws Exception {

		File[] fArray = dir.listFiles();
		for (int i = 0; i < fArray.length; i++) {
			File f = fArray[i];
			if (fArray[i].isDirectory()) {
				filesToZip = Converters.zipPrep(stem, f, filesToZip);
			} else {
				String s = f.getPath();
				if (s.startsWith(stem))
					s = s.substring(stem.length() + 1);
				filesToZip.put(s, f);
			}
		}

		return filesToZip;

	}

	public static void zipIt(Map<String, File> filesToZip, File targetZip)
			throws Exception {

		// Create a buffer for reading the files
		byte[] buf = new byte[1024];

		// Create the ZIP file
		ZipOutputStream out = new ZipOutputStream(new FileOutputStream(
				targetZip));

		// Compress the files
		Iterator<String> keyIt = filesToZip.keySet().iterator();
		while (keyIt.hasNext()) {
			String key = keyIt.next();
			File f = filesToZip.get(key);

			if( f.isDirectory() )
				continue;
			
			FileInputStream in = new FileInputStream(f);

			// Add ZIP entry to output stream.
			out.putNextEntry(new ZipEntry(key));

			// Transfer bytes from the file to the ZIP file
			int len;
			while ((len = in.read(buf)) > 0) {
				out.write(buf, 0, len);
			}

			// Complete the entry
			out.closeEntry();
			in.close();
		}

		// Complete the ZIP file
		out.close();

	}

	public static Map<String, File> unzipIt(File sourceZipFile,
			File unzipDestinationDirectory) throws Exception {

		Map<String, File> unzippedFiles = new HashMap<String, File>();

		//
		// zip file is contained inside a jar, this will generate an error.
		// need to copy the zip file out of the archive into a temporary
		// location.
		// - since this only occurs when the system is deployed in a jar,
		// we cannot write a unit test to recreate the bug.
		//
		File tempUnzippedDirectory = null;
		if (sourceZipFile.getPath().contains(".jar!")
				|| sourceZipFile.getPath().contains(".zip!")) {

			RandomStringGenerator rsg = new RandomStringGenerator.Builder() 
					.withinRange('0', 'z')
			        .filteredBy(LETTERS, DIGITS)
			        .build();
			String name = rsg.generate(10);
				    
			Path tempDirpath = Files.createTempDirectory(Paths.get(""), name);
			tempUnzippedDirectory = tempDirpath.toFile();
			
			String dAddr = tempUnzippedDirectory.getAbsolutePath();

			String wholePath = sourceZipFile.getPath();

			String jarPath = wholePath.substring(0, wholePath.indexOf("!"));
			if (jarPath.startsWith("file:"))
				jarPath = jarPath.substring(5);

			String entryPath = wholePath.substring(wholePath.indexOf("!") + 2,
					wholePath.length());

			entryPath = entryPath.replaceAll("\\\\", "/");

			// System.err.print("\n\n"+ entryPath + "\n\n");
			// System.err.print("\n\n"+ jarPath + "\n\n");

			JarFile jarFile = new JarFile(jarPath);
			ZipEntry entry = (ZipEntry) jarFile.getEntry(entryPath);

			BufferedInputStream is = new BufferedInputStream(
					jarFile.getInputStream(entry));
			int currentByte;

			// establish buffer for writing file
			byte data[] = new byte[BUFFER];

			// write the current file to disk
			FileOutputStream fos = new FileOutputStream(dAddr + "/"
					+ sourceZipFile.getName());
			BufferedOutputStream dest = new BufferedOutputStream(fos, BUFFER);

			// read and write until last byte is encountered
			while ((currentByte = is.read(data, 0, BUFFER)) != -1) {
				dest.write(data, 0, currentByte);
			}
			dest.flush();
			dest.close();
			is.close();

			// System.err.print(dAddr + "/" + sourceZipFile.getName());

			sourceZipFile = new File(dAddr + "/" + sourceZipFile.getName());

		}

		// Open Zip file for reading
		ZipFile zipFile = new ZipFile(sourceZipFile, ZipFile.OPEN_READ);

		// Create an enumeration of the entries in the zip file
		Enumeration zipFileEntries = zipFile.entries();

		// Process each entry
		while (zipFileEntries.hasMoreElements()) {

			// grab a zip file entry
			ZipEntry entry = (ZipEntry) zipFileEntries.nextElement();
			String currentEntry = entry.getName();
			File destFile = new File(unzipDestinationDirectory, currentEntry);

			// grab file's parent directory structure
			File destinationParent = destFile.getParentFile();

			// create the parent directory structure if needed
			destinationParent.mkdirs();

			// extract file if not a directory
			if (!entry.isDirectory()) {

				BufferedInputStream is = new BufferedInputStream(
						zipFile.getInputStream(entry));
				int currentByte;

				// establish buffer for writing file
				byte data[] = new byte[BUFFER];

				// write the current file to disk
				FileOutputStream fos = new FileOutputStream(destFile);
				BufferedOutputStream dest = new BufferedOutputStream(fos,
						BUFFER);

				// read and write until last byte is encountered
				while ((currentByte = is.read(data, 0, BUFFER)) != -1) {
					dest.write(data, 0, currentByte);
				}
				dest.flush();
				dest.close();
				is.close();

				unzippedFiles.put(destFile.getPath(), destFile);

			}

		}

		zipFile.close();

		if (tempUnzippedDirectory != null)
			Converters.recursivelyDeleteFiles(tempUnzippedDirectory);

		return unzippedFiles;

	}

	public static void cleanItUp(Map<String, File> filesToClean) {

		Set<String> dirPathSet = new HashSet<String>();

		// Order and delete files in reverse order of their paths
		String[] filePaths = (String[]) filesToClean.keySet().toArray(
				new String[0]);
		Arrays.sort(filePaths);
		for (int i = filePaths.length - 1; i >= 0; i--) {
			String p = filePaths[i];
			File f = filesToClean.get(p);
			f.delete();

			dirPathSet.add(f.getParent());

		}

	}

	public static void printEnvironment() {
		System.out.println("SYSTEM ENVIRONMENT");
		System.out.println("  Operating System: "
				+ System.getProperty("os.name"));
		System.out.println("  Architecture: " + System.getProperty("os.arch"));
		System.out.println("  Version: " + System.getProperty("os.version"));
		System.out.println("  User Dir: " + System.getProperty("user.dir"));
		System.out.println("  Classpath: ");
		String[] stack = System.getProperty("java.class.path").split(";");

		for (int i = 0; i < stack.length; i++)
			System.out.println("    " + stack[i]);

	}

	/**
	 * Convert the input string as a valid file name.
	 * 
	 * Replace invalid characters that cannot be part of the file name with "_".
	 * 
	 * @param fileName
	 *            String
	 * @return String
	 */
	public static String toValidFileName(String fileName) {
		String validName = null;

		//
		// For Windows machines, those invalid characters are:
		// /?<>\:*|".
		//
		if (System.getProperty("os.name").startsWith("Windows")) {

			validName = fileName.replaceAll("[\\/\\?<>\\\\:\\*|\"\\.]", "_");

			//
			// For Mac machines, those invalid characters are:
			// :.
			//
		} else if (System.getProperty("mrj.version") != null) {

			validName = fileName.replaceAll("[:\\.]", "_");

		}

		return validName;
	}

	public static String htmlify(String in) {
		return "<html><body>" + in + "</body></html>";
	}

	public static String fontTag() {
		return "<FONT size=\""
				+ HTML_TEXT_SIZE
				+ "\" face=\"Helvetica,Geneva, Arial,SunSans-Regular,sans-serif\">";
	}

	public static String htmlifyLabel(String in) {

		return Converters.htmlifyLabel(in, null, null);

	}

	public static String htmlifyLabel(String in, String extraTags,
			String tagTarget) {

		Pattern rlnPatt = Pattern.compile("(.*) \\>\\>\\> (.*) \\>\\>\\> (.*)");
		Matcher rlnMch = rlnPatt.matcher(in);

		Pattern multPatt = Pattern.compile("(.*) ... to ... (.*)");
		Matcher multMch = multPatt.matcher(in);
		String open = fontTag();
		String close = "</font>";

		if (extraTags != null) {
			for (int i = 0; i < extraTags.length(); i++) {
				open += "<" + extraTags.substring(i, i + 1) + ">";
				close += "</" + extraTags.substring(i, i + 1) + ">";
			}
		}

		String s = "<TR>";

		if (multMch.find()) {

			s += "<TD>" + open;
			s += multMch.group(1);
			s += close + "</TD><TD> ... to ... " + close + "</TD><TD>" + open;
			s += multMch.group(2);
			s += close + "</TD>";

		} else if (tagTarget != null) {

			if (rlnMch.find()) {

				s += "<TD>" + open;
				s += rlnMch.group(1);
				s += close + "</TD><TD>" + open + "<A href=\"" + tagTarget
						+ "\">";
				s += rlnMch.group(2);
				s += "</A>" + close + "</TD><TD>" + open;
				s += rlnMch.group(3);
				s += close + "</TD>";

			} else

				s += "<TD>" + open + "<A href=\"" + tagTarget + "\">" + in
						+ "</A>" + close + "</TD>";

		} else {

			if (rlnMch.find()) {
				s += "<TD>" + open;
				s += rlnMch.group(1);
				s += close + "</TD><TD>" + open;
				s += rlnMch.group(2);
				s += close + "</TD><TD>" + open;
				s += rlnMch.group(3);
				s += close + "</TD>";
			} else
				s += "<TD>" + open + in + close + "</TD>";

		}

		s += "</TR>";

		return s;

	}

	public static String separateString(String s, int lineLength,
			String separator) {
		String newLine = "";
		String out = "";
		Pattern p1 = Pattern.compile("[\\s]");
		Pattern p2 = Pattern.compile("[A-Z]");
		for (int i = 0; i < s.length(); i++) {
			String temp = s.substring(i, i + 1);
			Matcher m1 = p1.matcher(temp);
			Matcher m2 = p2.matcher(temp);
			if (newLine.length() > lineLength && m1.find()) {
				out += newLine + separator;
				newLine = "";
			} else if (newLine.length() > lineLength && m2.find()) {
				out += newLine + "-" + separator;
				newLine = "";
			}

			newLine += temp;
		}
		out += newLine;
		return out;
	}

	public static byte[] objectToByteArray(Object obj) throws Exception {

		ByteArrayOutputStream bos = null;
		ObjectOutputStream oos = null;
		BufferedImage img = null;
		ByteArrayOutputStream baos = null;

		try {

			bos = new ByteArrayOutputStream();
			oos = new ObjectOutputStream(bos);
			oos.writeObject(obj);
			return bos.toByteArray();

		} catch (IOException e) {

			e.printStackTrace();
			throw new Exception(e.getClass().getName() + ": " + e.getMessage());

		} finally {

			try {
				bos.close();
				oos.close();
			} catch (Exception ex) {
				throw new Exception(ex.getMessage());
			}

			bos = null;
			oos = null;

		}

	}

	public static Object byteArrayToObject(byte[] byteArray) throws Exception {

		//
		// Remember: do not leave local variables in the static
		// method especially when they store large data.
		//
		ByteArrayInputStream bis = null;
		ObjectInputStream ois = null;

		try {

			bis = new ByteArrayInputStream(byteArray);
			ois = new ObjectInputStream(bis);
			return ois.readObject();

		} catch (IOException e) {
			throw new Exception(e.getMessage());
		} catch (ClassNotFoundException cnfe) {
			throw new Exception(cnfe.getMessage());
		} finally {

			try {
				bis.close();
				ois.close();
			} catch (Exception ex) {
				throw new Exception(ex.getMessage());
			}

			bis = null;
			ois = null;

		}

	}

	public static String pkg2Uri(String stem, String pkg, String toStrip)
			throws Exception {

		String uri = "http://";

		if (!pkg.startsWith(stem))
			throw new Exception(pkg + " must start with " + stem);

		String[] stemPkgs = stem.split("\\.");
		for (int i = stemPkgs.length - 1; i >= 0; i--) {
			uri += stemPkgs[i];
			if (i > 0)
				uri += ".";
		}

		uri += "/";

		int j = 0;
		String rem = pkg.substring(stem.length() + 1);
		String[] remPkgs = rem.split("\\.");
		for (int i = 0; i < remPkgs.length; i++) {
			if (remPkgs[i].equals(toStrip)) {
				j++;
				continue;
			}
			uri += remPkgs[i] + "/";
		}

		return uri.substring(0, uri.length() - 1);
	}

	public static String xmlToString(Document xml) throws Exception {
		DOMImplementationRegistry registry = DOMImplementationRegistry
				.newInstance();
		DOMImplementationLS impl = (DOMImplementationLS) registry
				.getDOMImplementation("LS");
		LSSerializer writer = impl.createLSSerializer();
		String str = writer.writeToString(xml);
		return str;
	}

	public static Document stringToXml(String xmlSource) throws Exception {
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = factory.newDocumentBuilder();
		return builder.parse(new InputSource(new StringReader(xmlSource)));

	}

	public static void copyFile(File sourceFile, File destFile)
			throws IOException {
		if (!destFile.exists()) {
			destFile.createNewFile();
		}

		FileChannel source = null;
		FileChannel destination = null;

		try {
			source = new FileInputStream(sourceFile).getChannel();
			destination = new FileOutputStream(destFile).getChannel();
			destination.transferFrom(source, 0, source.size());
		} finally {
			if (source != null) {
				source.close();
			}
			if (destination != null) {
				destination.close();
			}
		}
	}

	public static String checksum(File f) throws FileNotFoundException, IOException {

		CheckedInputStream cis = cis = new CheckedInputStream(
				new FileInputStream(f), 
				new Adler32()
				);
		
		return Converters.checksum(cis);
	
	}

	private static String checksum(CheckedInputStream cis) throws IOException {
		String checksum = null;

		byte[] buf = new byte[128];
		while (cis.read(buf) >= 0) {
			// just read it.
		}
		checksum = String.valueOf(cis.getChecksum().getValue());
		
		return checksum;
	}

	private String getChecksum(byte[] byteData) throws FileNotFoundException, IOException {

		if (byteData == null) {
			return null;
		}

		CheckedInputStream cis = null;
		cis = new CheckedInputStream(
				new ByteArrayInputStream(byteData),
				new Adler32()
				);
	
		return Converters.checksum(cis);
	}

	public static File retrieveFileFromArchive(File f) throws IOException {
		
		RandomStringGenerator rsg = new RandomStringGenerator.Builder() 
				.withinRange('0', 'z')
		        .filteredBy(LETTERS, DIGITS)
		        .build();
		String name = rsg.generate(10);
			    
		Path tempDirpath = Files.createTempDirectory(Paths.get(""), name);
		File tempUnzippedDirectory = tempDirpath.toFile();

		String dAddr = tempUnzippedDirectory.getAbsolutePath();

		String wholePath = f.getPath();
		String jarPath = wholePath.substring(0, wholePath.indexOf("!"));
		if (jarPath.startsWith("file:"))
			jarPath = jarPath.substring(5);

		String entryPath = wholePath.substring(wholePath.indexOf("!") + 2,
				wholePath.length());

		entryPath = entryPath.replaceAll("\\\\", "/");

		JarFile jarFile = new JarFile(jarPath);
		ZipEntry entry = (ZipEntry) jarFile.getEntry(entryPath);

		BufferedInputStream is = new BufferedInputStream(
				jarFile.getInputStream(entry));
		int currentByte;

		// establish buffer for writing file
		byte data[] = new byte[BUFFER];

		// write the current file to disk
		FileOutputStream fos = new FileOutputStream(dAddr + "/"
				+ f.getName());
		BufferedOutputStream dest = new BufferedOutputStream(fos, BUFFER);

		// read and write until last byte is encountered
		while ((currentByte = is.read(data, 0, BUFFER)) != -1) {
			dest.write(data, 0, currentByte);
		}
		dest.flush();
		dest.close();
		is.close();

		return new File(dAddr + "/" + f.getName());
		
	}
	
	public static <T extends Comparable<? super T>> List<T> asSortedList(Collection<T> c) {
		  List<T> list = new ArrayList<T>(c);
		  java.util.Collections.sort(list);
		  return list;
		}
	
	public static URI convertUmlAddressToUri(String path) throws Exception {
		
		if( path.startsWith("|.") ) {
			path = path.substring(2,path.length());
		}
		
		Pattern pattern = Pattern.compile("\\.model(\\.|$)");
		Matcher matcher = pattern.matcher(path);
		int modelPos = -1;
		int modelLength = -1;
		if( matcher.find() ) { 
			modelPos = matcher.start();
			modelLength = 7;
		} else { 
			modelPos = path.lastIndexOf(".");
			modelLength = 0;
		}
		
		URI uri = null;
		
		String url = "http://";
		String pre = path.substring(0, modelPos);
		String[] bits = pre.split("\\.");
		
		for(int i=bits.length-2; i>=0; i--) {
			url += bits[i] + "." ;
		}
		url = url.substring(0, url.length()-1 ) + "/" + bits[bits.length-1] + "/";
		
		if(modelPos+modelLength < path.length()){ 
			String post = path.substring(modelPos + modelLength, path.length());
			url += post.replaceAll("\\.", "/");
		}
		uri = new URI(url);
		
		return uri;
	
	}

}
