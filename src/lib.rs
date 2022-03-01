// Copyright 2022 Anicet Ebou.
// Licensed under the MIT license (http://opensource.org/licenses/MIT)
// This file may not be copied, modified, or distributed
// except according to those terms.

//! We are describing structs and trait to read and write files in Catfish format.
//!
//! The Catfish format is a directed acyclic graph file format introduced by
//! Mingfu Shao and Carl Kingsford (https://github.com/Kingsford-Group/catfish).
//!
//! A multiple directed acyclic graph file in catfish format is composed of multiple graphs
//! represented here as a record. A record is composed of three main parts:
//!   - The header: The graph name and some comments. Some files headers are multiline.
//!   - The number of vertices (nodes)
//!   - The edges: Each following line is an edge composed of an in-vertex, an out-vertex and the weight of this edge
//!
//! This implementation takes into account the original file description and some
//! variants observed. For example, orignaly, the Catfish file header is limited to one line and
//! the vertices are named from 0 to n - 1 with n the number of vertices. Although, some files contains
//! multiline header and the vertices are characters.
//!
//! In this implementation vertices names are considered as String allowing to support both type of variants
//! and multiline header is supported.
//!
//! # Example
//!
//! ## Read
//!
//! We parse a Catfish file from stdin
//!
//! ```
//! use std::io;
//! use catfish::Reader;
//!
//! let mut reader = catfish::Reader::new(io::stdin());
//!
//! for result in reader.records() {
//!     let record = result.expect("Error parsing DAG record");
//!     println!("Graph header: {}\nNumber of vertices: {}\nEdges: {:#?}", record.header(), record.num_vertices(), record.edges());
//! }
//! ```
//!
//! We can also use a `while` loop
//!
//! ```
//! use std::io;
//! use catfish::Reader;
//!
//! let mut records = catfish::Reader::new(io::stdin()).records();
//!
//! while let Some(Ok(record)) = records.next() {
//!     println!("Graph header: {}\nNumber of vertices: {}\nEdges: {:#?}", record.header(), record.num_vertices(), record.edges());
//! }
//! ```
//!
//! ## Write
//!
//!
//! ```
//! use std::io;
//! use catfish::Writer;
//!
//! let mut writer = catfish::Writer::new(io::stdout());
//!
//! writer.write("graph 1",
//!              5,
//!              vec![("0", "1", "2"), ("0", "2", "3"), ("0", "3", "5"),
//!                   ("1", "2", "2"), ("1", "3", "4"), ("2", "3", "2"),
//!                   ("2", "4", "3"), ("3", "4", "7")]
//! );
//!```
//!
mod error;

use error::CatfishError;
use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::io;
use std::io::Write;
use std::path::Path;

/// A Catfish graph record
#[derive(Default, Debug, Clone)]
pub struct Record {
    /// The file header
    header: String,

    /// The number of vertices
    num_vertices: usize,

    /// The edges data
    edges: Vec<(String, String, String)>,
}

impl Record {
    /// Constructs a new Record.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::new();
    /// ```
    pub fn new() -> Self {
        Record {
            header: String::new(),
            num_vertices: 0_usize,
            edges: Vec::new(),
        }
    }

    /// Create a new record with attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::with_attrs("graph 1", 2, vec![("0", "1", "3"), ("1", "2", "3")]);
    /// ```
    pub fn with_attrs(header: &str, num_vertices: usize, edges: Vec<(&str, &str, &str)>) -> Self {
        let mut e = Vec::new();

        for (xi, xo, w) in edges {
            e.push((xi.to_string(), xo.to_string(), w.to_string()));
        }

        Record {
            header: header.to_owned(),
            num_vertices,
            edges: e,
        }
    }

    /// Check if record is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::new();
    /// assert!(record.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_vertices == 0_usize && self.edges.is_empty()
    }

    /// Check validity of Catfish graph record.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::with_attrs("graph 1", 3, vec![("0", "1", "3"), ("1", "2", "3")]);
    /// record.check().unwrap();
    /// ```
    pub fn check(&self) -> Result<(), &str> {
        if self.num_vertices == 0 {
            return Err("Expecting number of vertices different from 0 for Graph");
        }

        let mut uniques: HashSet<String> = HashSet::new();

        for (in_vertex, out_vertex, _) in &self.edges {
            uniques.insert(in_vertex.clone());
            uniques.insert(out_vertex.clone());
        }

        if self.num_vertices != uniques.len() {
            return Err(
                "Expecting the number of vertices to be equal to the vertices used in edges",
            );
        }

        Ok(())
    }

    /// Get header of a Catfish DAG.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::with_attrs("graph 1", 2, vec![("0", "1", "3"), ("1", "2", "3")]);
    /// assert_eq!(record.header(), "graph 1".to_string());
    /// ```
    pub fn header(&self) -> String {
        self.header.clone()
    }

    /// Get number of vertices (nodes) of a Catfish DAG.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::with_attrs("graph 1", 2, vec![("0", "1", "3"), ("1", "2", "3")]);
    ///
    /// assert_eq!(record.num_vertices(), 2);
    /// ```
    pub fn num_vertices(&self) -> usize {
        self.num_vertices
    }

    pub fn vertices(&self) -> HashSet<String> {
        let mut vertices = HashSet::new();

        for (in_vertex, out_vertex, _) in &self.edges {
            vertices.insert(in_vertex.clone());
            vertices.insert(out_vertex.clone());
        }

        vertices
    }

    pub fn edges(&self) -> Vec<(String, String, String)> {
        self.edges.clone()
    }

    /// Clear the record.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let mut record = Record::new();
    /// record.clear();
    /// ```
    pub fn clear(&mut self) {
        self.header.clear();
        self.num_vertices = 0;
        self.edges.clear();
    }

    #[cfg(feature = "graph")]
    /// Transform Catfish graph record to Petgraph Graph
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Record;
    ///
    /// let record = Record::new();
    ///
    /// let pg = record.to_graph();
    /// ```
    pub fn to_graph(&self) -> petgraph::Graph<&str, &str> {
        let mut ograph = petgraph::graph::DiGraph::new();

        for (in_vertex, out_vertex, weight) in &self.edges {
            let n1 = ograph.add_node(in_vertex.as_str());
            let n2 = ograph.add_node(out_vertex.as_str());
            ograph.add_edge(n1, n2, weight.as_str());
        }

        ograph
    }
}

// Display implementation for a Catfish record.
impl fmt::Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let edge: String = self
            .edges
            .iter()
            .map(|x| format!("{}\t{}\t{}", x.0, x.1, x.2))
            .collect();

        write!(f, "#{}\n{}\n{}", self.header, self.num_vertices, edge)
    }
}

/***************************************** Reader *****************************************/

/// Trait for Catfish readers.
pub trait CatfishRead {
    fn read(&mut self, record: &mut Record) -> Result<(), CatfishError>;
}

/// A Catfish reader.
#[derive(Debug)]
pub struct Reader<B> {
    reader: B,
    line: String,
}

impl Reader<io::BufReader<fs::File>> {
    /// Read Catfish file from given file path
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Reader;
    ///
    /// let reader = Reader::from_file("test/example.sgr");
    /// ```
    pub fn from_file<P: AsRef<Path> + std::fmt::Debug>(
        path: P,
    ) -> Result<Reader<io::BufReader<fs::File>>, io::Error> {
        fs::File::open(&path).map(Reader::new)
    }
}

impl<R> Reader<io::BufReader<R>>
where
    R: io::Read,
{
    /// Create a new Catfish reader given an instance of `io::Read`.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Reader;
    /// use std::io;
    ///
    /// let reader = Reader::new(io::stdin());
    /// ```
    pub fn new(reader: R) -> Self {
        Reader {
            reader: io::BufReader::new(reader),
            line: String::new(),
        }
    }
}

impl<B> Reader<B>
where
    B: io::BufRead,
{
    pub fn from_bufread(bufreader: B) -> Self {
        Reader {
            reader: bufreader,
            line: String::new(),
        }
    }

    pub fn records(self) -> Records<B> {
        Records {
            reader: self,
            error_has_occured: false,
        }
    }
}

impl<B> CatfishRead for Reader<B>
where
    B: io::BufRead,
{
    fn read(&mut self, record: &mut Record) -> Result<(), CatfishError> {
        // Clearing any data
        record.clear();

        // If line is empty, read a new line from buffer
        // if this newline is empty we are at end of file
        if self.line.is_empty() {
            self.reader.read_line(&mut self.line).map_err(|e| {
                CatfishError::UnexpectedError(Box::new(e), "Failed to read a new line".into())
            })?;
            if self.line.is_empty() {
                return Ok(());
            }
        }

        // If the first line does not starts with #, then
        // then the file is not correcly formatted
        if !self.line.starts_with('#') {
            return Err(CatfishError::ValidationError(
                "Failed to parse file. Missing '#' at start.".to_string(),
            ));
        }

        // The file can have multiline header
        // We then loop on theses lines
        loop {
            // If the line does not starts with # exit
            if !self.line.starts_with('#') {
                // Removing last leading whitespace before returning
                record.header = record.header.trim_start().to_string();

                break;
            }

            // Concatenate the header lines into one line
            // by removing first caracter (#) and trailing white space
            record.header.push_str(self.line[1..].trim_end());

            // Clear the readed line
            self.line.clear();

            // Read a new line
            self.reader.read_line(&mut self.line).map_err(|e| {
                CatfishError::UnexpectedError(Box::new(e), "Failed to read a new line".into())
            })?;
        }

        // Get vertice number and convert to u64
        record.num_vertices = self.line.trim().parse::<usize>().map_err(|e| {
            CatfishError::UnexpectedError(Box::new(e), "Failed to parse vertice number".into())
        })?;

        loop {
            self.line.clear();
            self.reader.read_line(&mut self.line).map_err(|e| {
                CatfishError::UnexpectedError(Box::new(e), "Failed to read a new line".into())
            })?;

            if self.line.is_empty() || self.line.starts_with('#') {
                break;
            }

            let elements: Vec<&str> = self.line.trim().split(' ').collect();

            record.edges.push((
                elements[0].to_owned(),
                elements[1].to_owned(),
                elements[2].to_owned(),
            ))
        }

        Ok(())
    }
}

pub struct Records<B>
where
    B: io::BufRead,
{
    reader: Reader<B>,
    error_has_occured: bool,
}

impl<B> Iterator for Records<B>
where
    B: io::BufRead,
{
    type Item = io::Result<Record>;

    fn next(&mut self) -> Option<io::Result<Record>> {
        if self.error_has_occured {
            None
        } else {
            let mut record = Record::new();
            match self.reader.read(&mut record) {
                Ok(()) if record.is_empty() => None,
                Ok(()) => Some(Ok(record)),
                Err(err) => {
                    self.error_has_occured = true;
                    Some(Err(io::Error::new(io::ErrorKind::Other, err.to_string())))
                }
            }
        }
    }
}

/***************************************** Writer *****************************************/

/// A Catfish writer.
#[derive(Debug)]
pub struct Writer<W: io::Write> {
    writer: io::BufWriter<W>,
}

impl Writer<fs::File> {
    /// Write to the given file path.
    pub fn to_file<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        fs::File::create(path).map(Writer::new)
    }
}

impl<W: io::Write> Writer<W> {
    /// Create a new Catfish writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Writer;
    /// use std::io;
    ///
    /// let writer = Writer::new(io::stdout());
    /// ```
    pub fn new(writer: W) -> Self {
        Writer {
            writer: io::BufWriter::new(writer),
        }
    }

    pub fn from_bufwriter(bufwriter: io::BufWriter<W>) -> Self {
        Writer { writer: bufwriter }
    }

    /// Write a new record
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::{Record, Writer};
    /// use std::io;
    ///
    /// let record = Record::new();
    /// let mut writer = Writer::new(io::stdout());
    ///
    /// writer.write_record(&record).unwrap();
    /// ```
    pub fn write_record(&mut self, record: &Record) -> io::Result<()> {
        let mut rec = Vec::new();
        let edges = record.edges();

        for (in_vertex, out_vertex, weight) in &edges {
            rec.push((in_vertex.as_str(), out_vertex.as_str(), weight.as_str()));
        }

        self.write(&record.header(), record.num_vertices(), rec)
    }

    /// Write a new record by using attributes
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Writer;
    /// use std::io;
    ///
    /// let mut writer = Writer::new(io::stdout());
    ///
    /// writer.write("graph1", 2, vec![("1", "2", "3"), ("1", "2", "3")]).unwrap();
    /// ```
    pub fn write(
        &mut self,
        header: &str,
        num_vertices: usize,
        edges: Vec<(&str, &str, &str)>,
    ) -> io::Result<()> {
        // Doing something like this, only allocate to create the final String.
        let chunks = header
            .chars()
            .collect::<Vec<char>>()
            .chunks(60)
            .map(|c| c.iter().collect::<String>())
            .collect::<Vec<String>>();

        for chunk in chunks {
            self.writer.write_all(b"# ")?;
            self.writer.write_all(chunk.as_bytes())?;
            self.writer.write_all(b"\n")?;
        }

        self.writer.write_all(num_vertices.to_string().as_bytes())?;

        for (in_vertex, out_vertex, weight) in edges {
            self.writer
                .write_fmt(format_args!("\n{} {} {}", in_vertex, out_vertex, weight))?;
        }

        Ok(())
    }

    /// Flush the writer, ensuring that everything is written.
    ///
    /// # Examples
    ///
    /// ```
    /// use catfish::Writer;
    /// use std::io;
    ///
    /// let mut writer = Writer::new(io::stdout());
    /// writer.flush();
    /// ```
    pub fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn test_read() {
        let mut reader = Reader::from_file("test/example.sgr").unwrap();
        let mut record = Record::new();

        reader.read(&mut record).expect("got an io::Error");
        assert_eq!(record.header(), "example 1 comment".to_string());
        assert_eq!(record.num_vertices(), 5);
        assert_eq!(
            record.edges(),
            vec![
                ("0".to_string(), "1".to_string(), "2".to_string()),
                ("0".to_string(), "2".to_string(), "3".to_string()),
                ("0".to_string(), "3".to_string(), "5".to_string()),
                ("1".to_string(), "2".to_string(), "2".to_string()),
                ("1".to_string(), "3".to_string(), "4".to_string()),
                ("2".to_string(), "3".to_string(), "2".to_string()),
                ("2".to_string(), "4".to_string(), "3".to_string()),
                ("3".to_string(), "4".to_string(), "7".to_string())
            ]
        );
    }

    #[test]
    fn test_records() {
        let reader = Reader::from_file("test/example.sgr").unwrap();
        let records = reader.records();

        let mut h = Vec::new();
        let mut n = Vec::new();
        let mut e = Vec::new();

        for result in records {
            let record = result.unwrap();
            h.push(record.header());
            n.push(record.num_vertices());
            e.push(record.edges());
        }

        assert_eq!(h[0], "example 1 comment".to_string());
        assert_eq!(h[1], "example 1".to_string());
        assert_eq!(h[2], "example 2".to_string());

        assert_eq!(n[0], 5);
        assert_eq!(n[1], 5);
        assert_eq!(n[2], 5);

        assert_eq!(
            e[0],
            vec![
                ("0".to_string(), "1".to_string(), "2".to_string()),
                ("0".to_string(), "2".to_string(), "3".to_string()),
                ("0".to_string(), "3".to_string(), "5".to_string()),
                ("1".to_string(), "2".to_string(), "2".to_string()),
                ("1".to_string(), "3".to_string(), "4".to_string()),
                ("2".to_string(), "3".to_string(), "2".to_string()),
                ("2".to_string(), "4".to_string(), "3".to_string()),
                ("3".to_string(), "4".to_string(), "7".to_string())
            ]
        );

        assert_eq!(
            e[1],
            vec![
                ("0".to_string(), "1".to_string(), "2".to_string()),
                ("0".to_string(), "2".to_string(), "3".to_string()),
                ("0".to_string(), "3".to_string(), "5".to_string()),
                ("1".to_string(), "2".to_string(), "2".to_string()),
                ("1".to_string(), "3".to_string(), "4".to_string()),
                ("2".to_string(), "3".to_string(), "2".to_string()),
                ("2".to_string(), "4".to_string(), "3".to_string()),
                ("3".to_string(), "4".to_string(), "7".to_string())
            ]
        );

        assert_eq!(
            e[2],
            vec![
                ("0".to_string(), "1".to_string(), "2".to_string()),
                ("0".to_string(), "2".to_string(), "3".to_string()),
                ("0".to_string(), "3".to_string(), "5".to_string()),
                ("1".to_string(), "2".to_string(), "2".to_string()),
                ("1".to_string(), "3".to_string(), "4".to_string()),
                ("2".to_string(), "3".to_string(), "2".to_string()),
                ("2".to_string(), "4".to_string(), "3".to_string()),
                ("3".to_string(), "4".to_string(), "7".to_string())
            ]
        );
    }

    #[test]
    fn test_write() {
        let file = NamedTempFile::new().unwrap();
        let mut writer = Writer::to_file(file.path()).unwrap();

        writer
            .write("graph 1", 2, vec![("a", "b", "c"), ("b", "c", "d")])
            .unwrap();

        writer.flush().unwrap();

        let mut reader = Reader::from_file(file.path()).unwrap();
        let mut record = Record::new();

        reader.read(&mut record).expect("got an io::Error");

        assert_eq!(record.header(), "graph 1".to_string());
        assert_eq!(record.num_vertices(), 2);
        assert_eq!(
            record.edges(),
            vec![
                ("a".to_string(), "b".to_string(), "c".to_string()),
                ("b".to_string(), "c".to_string(), "d".to_string())
            ]
        );
    }
}
