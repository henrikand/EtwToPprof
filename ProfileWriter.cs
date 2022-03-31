// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

using Google.Protobuf;
using pb = Google.Pprof.Protobuf;

using Microsoft.Windows.EventTracing;
using Microsoft.Windows.EventTracing.Cpu;
using Microsoft.Windows.EventTracing.Processes;
using Microsoft.Windows.EventTracing.Symbols;

using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text.RegularExpressions;

namespace EtwToPprof
{
  class ProfileWriter
  {
    public struct Options
    {
      public string etlFileName { get; set; }
      public bool includeInlinedFunctions { get; set; }
      public bool includeProcessIds { get; set; }
      public bool includeProcessAndThreadIds { get; set; }
      public bool splitChromeProcesses { get; set; }
      public string stripSourceFileNamePrefix { get; set; }
      public decimal timeStart { get; set; }
      public decimal timeEnd { get; set; }
      public HashSet<string> processFilterSet { get; set; }
      public decimal? processIdFilter { get; set; }
    }

    public ProfileWriter(Options options)
    {
      this._options = options;

      _stripSourceFileNamePrefixRegex = new Regex(_options.stripSourceFileNamePrefix,
                                                  RegexOptions.Compiled | RegexOptions.IgnoreCase);

      _profile = new pb.Profile();
      _profile.StringTable.Add("");
      _strings = new Dictionary<string, long>();
      _strings.Add("", 0);
      _nextStringId = 1;

      var cpuTimeValueType = new pb.ValueType();
      cpuTimeValueType.Type = GetStringId("cpu");
      cpuTimeValueType.Unit = GetStringId("nanoseconds");
      _profile.SampleType.Add(cpuTimeValueType);

      _locations = new Dictionary<Location, ulong>();
      _nextLocationId = 1;

      _functions = new Dictionary<Function, ulong>();
      _nextFunctionId = 1;
    }

    public void AddSample(ICpuSample sample)
    {
      if ((sample.IsExecutingDeferredProcedureCall ?? false) ||
          (sample.IsExecutingInterruptServicingRoutine ?? false))
        return;

      var timestamp = sample.Timestamp.RelativeTimestamp.TotalSeconds;
      if (timestamp < _options.timeStart || timestamp > _options.timeEnd)
        return;

      if (sample.Process == null)
        return;

      if (_options.processFilterSet != null && _options.processFilterSet.Count > 0)
      {
        var processImage = sample.Process.Images.FirstOrDefault(
            image => image.FileName == sample.Process.ImageName);

        string imagePath = processImage?.Path ?? sample.Process.ImageName;

        // In some rare cases sample.Process.ImageName can also be empty.
        if (string.IsNullOrEmpty(imagePath))
          return;

        if (!_options.processFilterSet.Any(filter => imagePath.Contains(filter.Replace("/", "\\"))))
          return;
      }

      // If a PID filter has been set, only allow one specific PID to pass.
      if (_options.processIdFilter.HasValue &&
          _options.processIdFilter.Value != sample.Process.Id) {
        return;
      }

      _wallTimeStart = Math.Min(_wallTimeStart, timestamp);
      _wallTimeEnd = Math.Max(_wallTimeEnd, timestamp);

      var sampleProto = new pb.Sample();
      sampleProto.Value.Add(sample.Weight.Nanoseconds);
      if (sample.Stack != null && sample.Stack.Frames.Count != 0)
      {
        int processId = sample.Process.Id;
        foreach (var stackFrame in sample.Stack.Frames)
        {
          if (stackFrame.HasValue && stackFrame.Symbol != null)
          {
            sampleProto.LocationId.Add(GetLocationId(stackFrame.Symbol));
          }
          else
          {
            string imageName = stackFrame.Image?.FileName ?? "<unknown>";
            string functionLabel = "<unknown>";
            sampleProto.LocationId.Add(
              GetPseudoLocationId(processId, imageName, null, functionLabel));
          }
        }
        string processName = sample.Process.ImageName;
        string threadLabel = sample.Thread?.Name;
        if (threadLabel == null || threadLabel == "")
          threadLabel = "anonymous thread";
        if (_options.includeProcessAndThreadIds)
        {
          threadLabel = String.Format("{0} ({1})", threadLabel, sample.Thread?.Id ?? 0);
        }
        sampleProto.LocationId.Add(
          GetPseudoLocationId(processId, processName, sample.Thread?.StartAddress, threadLabel));

        string processLabel = processName;
        if (_options.splitChromeProcesses && processName == "chrome.exe" &&
            sample.Process.CommandLine != null)
        {
          var commandLineSplit = sample.Process.CommandLine.Split();
          foreach (string commandLineArg in commandLineSplit)
          {
            const string kProcessTypeParam = "--type=";
            if (commandLineArg.StartsWith(kProcessTypeParam))
            {
              string chromeProcessType = commandLineArg.Substring(kProcessTypeParam.Length);

              const string kUtilityProcessType = "utility";
              const string kUtilitySubTypeParam = "--utility-sub-type=";
              if (chromeProcessType == kUtilityProcessType)
              {
                var utilitySubType = commandLineSplit.First(s => s.StartsWith(kUtilitySubTypeParam));
                if (utilitySubType != null)
                {
                  processLabel = processLabel +
                      $" ({utilitySubType.Substring(kUtilitySubTypeParam.Length)})";
                  break;
                }
              }

              processLabel = processLabel + $" ({chromeProcessType})";
            }
          }
        }
        if (_options.includeProcessIds || _options.includeProcessAndThreadIds)
        {
          processLabel = processLabel + $" ({processId})";
        }
        sampleProto.LocationId.Add(
          GetPseudoLocationId(processId, processName, sample.Process.ObjectAddress, processLabel));

        if (_processThreadCpuTimes.ContainsKey(processLabel))
        {
          Dictionary<string, decimal> threadCpuTimes = _processThreadCpuTimes[processLabel];
          if (threadCpuTimes.ContainsKey(threadLabel))
          {
            threadCpuTimes[threadLabel] += sample.Weight.TotalMilliseconds;
          }
          else
          {
            threadCpuTimes[threadLabel] = sample.Weight.TotalMilliseconds;
          }
        }
        else
        {
          _processThreadCpuTimes[processLabel] = new Dictionary<string, decimal>();
          _processThreadCpuTimes[processLabel][threadLabel] = sample.Weight.TotalMilliseconds;
        }

        if (_processCpuTimes.ContainsKey(processLabel))
        {
          _processCpuTimes[processLabel] += sample.Weight.TotalMilliseconds;
        }
        else
        {
          _processCpuTimes[processLabel] = sample.Weight.TotalMilliseconds;
        }

        _totalCpuTime += sample.Weight.TotalMilliseconds;
      }

      _profile.Sample.Add(sampleProto);
    }

    public long Write(string outputFileName)
    {
      _profile.Comment.Add(GetStringId($"Converted by EtwToPprof from {Path.GetFileName(_options.etlFileName)}"));
      if (_wallTimeStart < _wallTimeEnd)
      {
        decimal wallTimeMs = (_wallTimeEnd - _wallTimeStart) * 1000;
        _profile.Comment.Add(GetStringId($"Wall time {wallTimeMs:F} ms"));
        _profile.Comment.Add(GetStringId($"CPU time {_totalCpuTime:F} ms ({_totalCpuTime / wallTimeMs:P})"));

        var sortedProcesses = _processCpuTimes.Keys.ToList();
        sortedProcesses.Sort((a, b) => -_processCpuTimes[a].CompareTo(_processCpuTimes[b]));

        foreach (var processLabel in sortedProcesses)
        {
          decimal processCpuTime = _processCpuTimes[processLabel];
          _profile.Comment.Add(GetStringId($"  {processLabel} {processCpuTime:F} ms ({processCpuTime / wallTimeMs:P})"));

          var threadCpuTimes = _processThreadCpuTimes[processLabel];

          var sortedThreads = threadCpuTimes.Keys.ToList();
          sortedThreads.Sort((a, b) => -threadCpuTimes[a].CompareTo(threadCpuTimes[b]));

          foreach (var threadLabel in sortedThreads)
          {
            var threadCpuTime = threadCpuTimes[threadLabel];
            _profile.Comment.Add(GetStringId($"    {threadLabel} {threadCpuTime:F} ms ({threadCpuTime / wallTimeMs:P})"));
          }
        }
      }
      else
      {
        _profile.Comment.Add(GetStringId("No samples exported"));
      }
      using (FileStream output = File.Create(outputFileName))
      {
        using (GZipStream gzip = new GZipStream(output, CompressionMode.Compress))
        {
          using (CodedOutputStream serialized = new CodedOutputStream(gzip))
          {
            _profile.WriteTo(serialized);
            return output.Length;
          }
        }
      }
    }

    readonly struct Location
    {
      public Location(int processId, string imagePath, Address? functionAddress, string functionName)
      {
        ProcessId = processId;
        ImagePath = imagePath;
        FunctionAddress = functionAddress;
        FunctionName = functionName;
      }
      int ProcessId { get; }
      string ImagePath { get; }
      Address? FunctionAddress { get; }
      string FunctionName { get; }

      public override bool Equals(object other)
      {
        return other is Location l
               && l.ProcessId == ProcessId
               && l.ImagePath == ImagePath
               && l.FunctionAddress == FunctionAddress
               && l.FunctionName == FunctionName;
      }

      public override int GetHashCode()
      {
        return (ProcessId, ImagePath, FunctionAddress, FunctionName).GetHashCode();
      }
    }

    ulong GetPseudoLocationId(int processId, string imageName, Address? address, string label)
    {
      var location = new Location(processId, imageName, address, label);
      ulong locationId;
      if (!_locations.TryGetValue(location, out locationId))
      {
        locationId = _nextLocationId++;
        _locations.Add(location, locationId);

        var locationProto = new pb.Location();
        locationProto.Id = locationId;

        var line = new pb.Line();
        line.FunctionId = GetFunctionId(imageName, label);
        locationProto.Line.Add(line);

        _profile.Location.Add(locationProto);
      }
      return locationId;
    }

    ulong GetLocationId(IStackSymbol stackSymbol)
    {
      var processId = stackSymbol.Image?.ProcessId ?? 0;
      var imageName = stackSymbol.Image?.FileName;
      var imagePath = stackSymbol.Image?.Path ?? "<unknown>";
      var functionAddress = stackSymbol.AddressRange.BaseAddress;
      var functionName = stackSymbol.FunctionName;

      var location = new Location(processId, imagePath, functionAddress, functionName);

      ulong locationId;
      if (!_locations.TryGetValue(location, out locationId))
      {
        locationId = _nextLocationId++;
        _locations.Add(location, locationId);

        var locationProto = new pb.Location();
        locationProto.Id = locationId;

        pb.Line line;
        if (_options.includeInlinedFunctions && stackSymbol.InlinedFunctionNames != null)
        {
          foreach (var inlineFunctionName in stackSymbol.InlinedFunctionNames)
          {
            line = new pb.Line();
            line.FunctionId = GetFunctionId(imageName, inlineFunctionName);
            locationProto.Line.Add(line);
          }
        }
        line = new pb.Line();
        line.FunctionId = GetFunctionId(imageName, functionName, stackSymbol.SourceFileName);
        line.Line_ = stackSymbol.SourceLineNumber;
        locationProto.Line.Add(line);

        _profile.Location.Add(locationProto);
      }
      return locationId;
    }

    readonly struct Function
    {
      public Function(string imageName, string functionName)
      {
        ImageName = imageName;
        FunctionName = functionName;
      }
      string ImageName { get; }
      string FunctionName { get; }

      public override bool Equals(object other)
      {
        return other is Function f && f.ImageName == ImageName && f.FunctionName == FunctionName;
      }

      public override int GetHashCode()
      {
        return (ImageName, FunctionName).GetHashCode();
      }

      public override string ToString()
      {
        return String.Format("{0}!{1}", ImageName, FunctionName);
      }
    }

    ulong GetFunctionId(string imageName, string functionName, string sourceFileName = null)
    {
      ulong functionId;
      var function = new Function(imageName, functionName);
      if (!_functions.TryGetValue(function, out functionId))
      {
        var functionProto = new pb.Function();
        functionProto.Id = _nextFunctionId++;
        functionProto.Name = GetStringId(functionName ?? function.ToString());
        functionProto.SystemName = GetStringId(function.ToString());
        if (sourceFileName == null)
        {
          sourceFileName = imageName;
        }
        else
        {
          sourceFileName = sourceFileName.Replace('\\', '/');
          sourceFileName = _stripSourceFileNamePrefixRegex.Replace(sourceFileName, "");
        }
        functionProto.Filename = GetStringId(sourceFileName);

        functionId = functionProto.Id;
        _functions.Add(function, functionId);
        _profile.Function.Add(functionProto);
      }
      return functionId;
    }

    long GetStringId(string str)
    {
      long stringId;
      if (!_strings.TryGetValue(str, out stringId))
      {
        stringId = _nextStringId++;
        _strings.Add(str, stringId);
        _profile.StringTable.Add(str);
      }
      return stringId;
    }

    private readonly Options _options;

    Dictionary<Location, ulong> _locations;
    ulong _nextLocationId;

    Dictionary<Function, ulong> _functions;
    ulong _nextFunctionId;

    Dictionary<string, long> _strings;
    long _nextStringId;

    Regex _stripSourceFileNamePrefixRegex;

    decimal _wallTimeStart = decimal.MaxValue;
    decimal _wallTimeEnd = 0;

    decimal _totalCpuTime = 0;
    Dictionary<string, decimal> _processCpuTimes = new Dictionary<string, decimal>();
    Dictionary<string, Dictionary<string, decimal>> _processThreadCpuTimes = new Dictionary<string, Dictionary<string, decimal>>();

    pb.Profile _profile;
  }
}
