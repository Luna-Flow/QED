# QED

QED 是一个基于 MoonBit 语言开发的定理证明器（Theorem Prover）。

## 项目简介

该项目旨在为 MoonBit 生态系统提供形式化验证工具，支持数学定理的建模与证明。

## 项目结构

- **kernel/**: LCF 核心层，定义了 STT 的类型、项和原始推理规则。
- **logic/**: 逻辑层，基于内核构建基础逻辑常量和定义。
- **tactics/**: 策略层，辅助证明搜索的 Tactics 系统。
- **cmd/**: 命令行交互入口。

## 技术栈

- **核心语言**: [MoonBit](https://www.moonbitlang.com/)
- **逻辑系统**: Simple Type Theory (STT)
- **架构**: LCF-style Kernel

## 开始使用

```bash
moon build
moon test
```
