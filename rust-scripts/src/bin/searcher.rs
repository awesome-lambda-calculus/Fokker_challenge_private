use chrono::Local;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Serialize, Deserialize, Clone)]
struct MatchItem {
    full_word: String,
    extracted_prefix: String,
}

#[derive(Serialize, Deserialize, Clone)]
struct FileResult {
    filepath: PathBuf,
    matches: Vec<MatchItem>,
}

#[derive(Serialize, Deserialize)]
struct SearchResult {
    search_pattern: String,
    search_time: String,
    folder_scanned: PathBuf,
    total_files_with_matches: usize,
    total_matches_found: usize,
    results: Vec<FileResult>,
}

fn main() {
    let folder_path = ".."; // ← 修改成你的文件夹路径
    let file_extension: &OsStr = OsStr::new("lean");
    let output_file = "basis_extract_result.json";

    let pattern = r"(\w+)_is_not_basis";
    let regex = Regex::new(pattern).expect("Invalid regex");

    let mut results: Vec<FileResult> = Vec::new();
    let mut total_matches = 0;

    println!("开始扫描文件夹: {}", folder_path);

    for entry in WalkDir::new(folder_path).into_iter().filter_map(|e| e.ok()) {
        if !entry.file_type().is_file() {
            continue;
        }

        let path = entry.path();

        // 文件后缀过滤
        if path.extension() != Some(file_extension) {
            continue;
        }

        match fs::read_to_string(path) {
            Ok(content) => {
                let matches: Vec<_> = regex
                    .captures_iter(&content)
                    .filter_map(|cap| cap.get(1).map(|m| m.as_str().to_string()))
                    .collect();

                if !matches.is_empty() {
                    let file_matches: Vec<MatchItem> = matches
                        .iter()
                        .map(|prefix| MatchItem {
                            full_word: format!("{}_is_not_basis", prefix),
                            extracted_prefix: prefix.clone(),
                        })
                        .collect();

                    let file_result = FileResult {
                        filepath: path.to_path_buf(),
                        matches: file_matches,
                    };

                    results.push(file_result);
                    total_matches += matches.len();
                }
            }
            Err(e) => {
                eprintln!("读取文件失败 {}: {}", path.display(), e);
            }
        }
    }

    let search_result = SearchResult {
        search_pattern: "_is_not_basis".to_string(),
        search_time: Local::now().format("%Y-%m-%d %H:%M:%S").to_string(),
        folder_scanned: Path::new(folder_path)
            .canonicalize()
            .unwrap_or_else(|_| Path::new(folder_path).to_path_buf()),
        total_files_with_matches: results.len(),
        total_matches_found: total_matches,
        results,
    };

    match serde_json::to_string_pretty(&search_result) {
        Ok(json) => {
            if let Err(e) = fs::write(output_file, json) {
                eprintln!("写入 JSON 失败: {}", e);
            } else {
                println!("✅ 处理完成！");
                // println!("   发现匹配的文件: {} 个", results.len());
                println!("   总共提取前缀: {} 个", total_matches);
                println!("   输出文件: {}", output_file);
            }
        }
        Err(e) => eprintln!("JSON 序列化失败: {}", e),
    }
}
